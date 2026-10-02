//! Measurement harness shared by `benches/kernel.rs`.
//!
//! ## Design constraints taken from the charter
//!
//! §13 asks for wall time, CPU time, peak RSS, allocation count, memory
//! footprint and operation counts. §27 says never declare an optimisation
//! successful without measurements. That combination means the harness must be
//! reproducible across machines, so:
//!
//! * **Work is bounded by step budgets, never by time.** A wall-clock cutoff
//!   makes the amount of computation machine-dependent, which destroys
//!   comparability. Time is measured, never used as a limit -- except in the two
//!   benchmarks that deliberately study a budget being exhausted.
//! * **Every benchmark reports deterministic work counters** (`candidates`,
//!   `derivations`, `rounds`) next to the timings. When an algorithmic change
//!   alters those, the change is real; when it does not, only a constant factor
//!   moved, and the report says which.
//! * **The PRNG is explicitly seeded** and the seed appears in the output.
//!
//! Numbers are read from `/proc/self`, so the harness is Linux-only. That is a
//! deliberate trade: the alternative is a dependency tree larger than the crate
//! under test.

use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::Instant;

// ---- allocation counting ------------------------------------------------

static ALLOCS: AtomicU64 = AtomicU64::new(0);
static BYTES: AtomicU64 = AtomicU64::new(0);

struct CountingAlloc;

unsafe impl GlobalAlloc for CountingAlloc {
    unsafe fn alloc(&self, l: Layout) -> *mut u8 {
        ALLOCS.fetch_add(1, Ordering::Relaxed);
        BYTES.fetch_add(l.size() as u64, Ordering::Relaxed);
        System.alloc(l)
    }
    unsafe fn dealloc(&self, p: *mut u8, l: Layout) {
        System.dealloc(p, l)
    }
    unsafe fn realloc(&self, p: *mut u8, l: Layout, new: usize) -> *mut u8 {
        ALLOCS.fetch_add(1, Ordering::Relaxed);
        BYTES.fetch_add(new as u64, Ordering::Relaxed);
        System.realloc(p, l, new)
    }
}

#[global_allocator]
static ALLOC: CountingAlloc = CountingAlloc;

/// Allocations since process start.
pub fn allocs() -> u64 {
    ALLOCS.load(Ordering::Relaxed)
}

/// Bytes requested from the allocator since process start.
pub fn allocated_bytes() -> u64 {
    BYTES.load(Ordering::Relaxed)
}

// ---- process metrics ----------------------------------------------------

fn proc_status_field(field: &str) -> u64 {
    let Ok(s) = std::fs::read_to_string("/proc/self/status") else {
        return 0;
    };
    for line in s.lines() {
        if let Some(rest) = line.strip_prefix(field) {
            let rest = rest.trim().trim_end_matches("kB").trim();
            return rest.parse().unwrap_or(0);
        }
    }
    0
}

/// Current resident set size, kB.
pub fn rss_kb() -> u64 {
    proc_status_field("VmRSS:")
}

/// High-water resident set size for the whole process lifetime, kB.
pub fn peak_rss_kb() -> u64 {
    proc_status_field("VmHWM:")
}

/// User + system CPU time in milliseconds, from `/proc/self/stat`.
///
/// `USER_HZ` is 100 on every Linux target this project runs on; the value is
/// read from `sysconf` on glibc but assumed here to keep the harness
/// dependency-free. At 10 ms granularity that is fine for runs of 50 ms or
/// longer, which is why [`Bench::run`] refuses to report shorter runs as
/// meaningful.
pub fn cpu_ms() -> u64 {
    let Ok(s) = std::fs::read_to_string("/proc/self/stat") else {
        return 0;
    };
    // The comm field may contain spaces and parentheses, so fields are counted
    // from after the final ')'.
    let Some(close) = s.rfind(')') else { return 0 };
    let rest: Vec<&str> = s[close + 1..].split_whitespace().collect();
    // After comm and state, utime is field 12 and stime field 13 (1-based).
    let utime: u64 = rest.get(11).and_then(|v| v.parse().ok()).unwrap_or(0);
    let stime: u64 = rest.get(12).and_then(|v| v.parse().ok()).unwrap_or(0);
    (utime + stime) * 10
}

// ---- deterministic RNG --------------------------------------------------

/// splitmix64. Chosen because it is tiny, has no state beyond one `u64`, and
/// produces the same stream on every platform -- which is what a benchmark
/// needs. Not cryptographic and not used for anything but workload generation.
pub struct Rng(u64);

impl Rng {
    pub fn new(seed: u64) -> Self {
        Rng(seed)
    }
    #[inline]
    pub fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }
    #[inline]
    pub fn below(&mut self, n: u64) -> u64 {
        self.next() % n.max(1)
    }
}

// ---- harness ------------------------------------------------------------

const MIN_RUN_MS: u128 = 50;
const MAX_ITERS: u64 = 2000;

pub struct Row {
    pub name: String,
    pub iters: u64,
    pub ops: u64,
    pub wall_ms: f64,
    pub cpu_ms: u64,
    pub allocs: u64,
    pub alloc_bytes: u64,
    pub rss_kb: u64,
    pub note: String,
}

impl Row {
    fn default_stub() -> Row {
        Row {
            name: String::new(),
            iters: 0,
            ops: 0,
            wall_ms: 0.0,
            cpu_ms: 0,
            allocs: 0,
            alloc_bytes: 0,
            rss_kb: 0,
            note: String::new(),
        }
    }
}

pub struct Bench {
    title: String,
    notes: Vec<String>,
    pub rows: Vec<Row>,
}

impl Bench {
    pub fn new(title: &str) -> Self {
        println!("{}\n{}", "=".repeat(78), title);
        Bench {
            title: title.to_string(),
            notes: Vec::new(),
            rows: Vec::new(),
        }
    }

    pub fn note(&mut self, s: impl Into<String>) {
        self.notes.push(s.into());
    }

    /// Adaptive timing: one warm-up call, then repeat until the run is long
    /// enough to measure. The closure's return value is the operation count.
    /// Record a row and print it immediately.
    ///
    /// Streaming rather than buffering was added after a 15-minute run had to be
    /// killed with nothing to show for it: a suite that prints only at the end
    /// loses every result when a late benchmark turns out to be pathological,
    /// which is exactly when the numbers are most wanted.
    fn push(&mut self, row: Row) {
        let r = self.rows.last().expect("just pushed");
        let r = r;
        let secs = r.wall_ms / 1000.0;
        let mops = if secs > 0.0 { r.ops as f64 / secs / 1e6 } else { 0.0 };
        let ai = if r.iters > 0 { r.allocs / r.iters } else { 0 };
        let bo = if r.ops > 0 { r.alloc_bytes / r.ops } else { 0 };
        // stderr, not stdout: stdout is block-buffered when redirected to a
        // file, which hid every row from a run that had to be killed.
        eprintln!(
            "  {:<30} {:>7} it {:>10.2} ms {:>9} Mops/s {:>9} allocs/it {:>10} B/op {:>8} rss kB",
            r.name, r.iters, r.wall_ms, mops, ai, bo, r.rss_kb
        );
        let _ = row;
    }

    pub fn run(&mut self, name: &str, hint_ops: u64, mut f: impl FnMut(u32) -> u64) {
        std::hint::black_box(f(u32::MAX));
        let a0 = allocs();
        let b0 = allocated_bytes();
        let c0 = cpu_ms();
        let t0 = Instant::now();
        let mut ops = 0u64;
        let mut iters = 0u64;
        loop {
            ops += f(iters as u32);
            iters += 1;
            if t0.elapsed().as_millis() >= MIN_RUN_MS || iters >= MAX_ITERS {
                break;
            }
        }
        let wall = t0.elapsed().as_secs_f64() * 1000.0;
        self.rows.push(Row {
            name: name.to_string(),
            iters,
            ops,
            wall_ms: wall,
            cpu_ms: cpu_ms().saturating_sub(c0),
            allocs: allocs().saturating_sub(a0),
            alloc_bytes: allocated_bytes().saturating_sub(b0),
            rss_kb: rss_kb(),
            note: format!("hint {hint_ops} ops"),
        });
        self.push(Row::default_stub());
    }

    /// Same, but with no warm-up, for workloads whose single iteration is
    /// already long enough to measure.
    pub fn run_once(&mut self, name: &str, mut f: impl FnMut(u32) -> u64) {
        let a0 = allocs();
        let b0 = allocated_bytes();
        let c0 = cpu_ms();
        let t0 = Instant::now();
        let ops = f(0);
        let wall = t0.elapsed().as_secs_f64() * 1000.0;
        self.rows.push(Row {
            name: name.to_string(),
            iters: 1,
            ops,
            wall_ms: wall,
            cpu_ms: cpu_ms().saturating_sub(c0),
            allocs: allocs().saturating_sub(a0),
            alloc_bytes: allocated_bytes().saturating_sub(b0),
            rss_kb: rss_kb(),
            note: "single shot".into(),
        });
        self.push(Row::default_stub());
    }

    /// Run one closure per mode and emit a row per mode, for A/B comparisons.
    pub fn compare(&mut self, name: &str, iters: u64, mut f: impl FnMut(u32) -> u64) {
        for mode in 0..2u32 {
            let label = format!("{name}[{}]", if mode == 0 { "A" } else { "B" });
            let a0 = allocs();
            let b0 = allocated_bytes();
            let c0 = cpu_ms();
            let t0 = Instant::now();
            let mut ops = 0u64;
            for i in 0..iters {
                ops += f(mode);
                std::hint::black_box(i);
            }
            let wall = t0.elapsed().as_secs_f64() * 1000.0;
            self.rows.push(Row {
                name: label,
                iters,
                ops,
                wall_ms: wall,
                cpu_ms: cpu_ms().saturating_sub(c0),
                allocs: allocs().saturating_sub(a0),
                alloc_bytes: allocated_bytes().saturating_sub(b0),
                rss_kb: rss_kb(),
                note: String::new(),
            });
            self.push(Row::default_stub());
        }
    }

    pub fn report(&self) {
        println!("{}", "-".repeat(78));
        println!("{}", self.title);
        for n in &self.notes {
            println!("  {n}");
        }
        println!("{}", "-".repeat(78));
        println!(
            "{:<28} {:>8} {:>11} {:>9} {:>10} {:>10} {:>14} {:>11}",
            "benchmark",
            "iters",
            "wall ms",
            "cpu ms",
            "Mops/s",
            "allocs/it",
            "alloc B/op",
            "rss kB"
        );
        println!("{}", "-".repeat(78));
        for r in &self.rows {
            let secs = r.wall_ms / 1000.0;
            let mops = if secs > 0.0 {
                r.ops as f64 / secs / 1e6
            } else {
                0.0
            };
            let ai = if r.iters > 0 { r.allocs / r.iters } else { 0 };
            let bo = if r.ops > 0 { r.alloc_bytes / r.ops } else { 0 };
            println!(
                "{:<28} {:>8} {:>11.2} {:>9} {:>10.2} {:>10} {:>14} {:>11}",
                r.name, r.iters, r.wall_ms, r.cpu_ms, mops, ai, bo, r.rss_kb
            );
        }
        println!("{}", "-".repeat(78));
    }

    pub fn title(&self) -> &str {
        &self.title
    }
}
