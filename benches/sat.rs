//! The SAT-core benchmark: the frozen corpus in `data/`, solved at a fixed
//! step budget with deterministic work counters alongside the timings.
//! Correctness (labels, certificates) is asserted in `tests/sat.rs`, not
//! here; this measures cost. Run with `cargo bench --bench sat`.

use axiom::bench::Bench;
use axiom::sat::{parse_dimacs, verify_sat, verify_unsat, SatOutcome, SatSolver, SatStats};
use axiom::Budget;

const CORPUS: &[(&str, &str, bool)] = &[
    ("sat_trivial", include_str!("data/sat_trivial.cnf"), true),
    ("unsat_units", include_str!("data/unsat_units.cnf"), false),
    ("sat_xor2", include_str!("data/sat_xor2.cnf"), true),
    ("unsat_xor01", include_str!("data/unsat_xor01.cnf"), false),
    ("unsat_php32", include_str!("data/unsat_php32.cnf"), false),
    ("sat_chain7", include_str!("data/sat_chain7.cnf"), true),
];

fn main() {
    let mut b = Bench::new("axiom -- SAT core on the frozen corpus");
    b.note("single-threaded; work bounded by deterministic step budgets");
    b.note("labels and certificates asserted in tests/sat.rs; this measures cost");
    let mut solved = 0u64;
    for (name, src, expect_sat) in CORPUS {
        let (_, clauses) = parse_dimacs(src).expect("corpus parses");
        let mut last = SatStats::default();
        let mut ok = false;
        b.run_once(name, |_| {
            let mut s = SatSolver::new();
            for c in &clauses {
                s.add_clause(c);
            }
            let mut budget = Budget::steps(100_000_000);
            let ops = match s.solve(&mut budget) {
                Ok(SatOutcome::Sat { model }) => {
                    assert!(verify_sat(&clauses, &model));
                    assert!(*expect_sat, "corpus label flipped to sat");
                    ok = true;
                    s.stats.propagations + s.stats.decisions
                }
                Ok(SatOutcome::Unsat { proof }) => {
                    assert!(verify_unsat(&clauses, &proof).is_ok());
                    assert!(!expect_sat, "corpus label flipped to unsat");
                    ok = true;
                    s.stats.propagations + s.stats.conflicts
                }
                Err(_) => 0,
            };
            last = s.stats;
            ops
        });
        if ok {
            solved += 1;
        }
        println!(
            "    {name}: decisions={} conflicts={} propagations={} learned={} restarts={} deleted={}",
            last.decisions,
            last.conflicts,
            last.propagations,
            last.learned,
            last.restarts,
            last.deleted
        );
    }
    println!("\n  solved {solved} of {} corpus instances", CORPUS.len());
}
