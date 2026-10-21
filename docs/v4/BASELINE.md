# Axiom v4 — verified baseline

Baseline commit: `4c60f3fc1197f44028acf789a4794c5b886e2894` (`main`, 2026-10-11)
Baseline tag: `v4-baseline`
Measured: 2026-10-21 from CI run
[`38126488372`](https://github.com/mahithpaulin/axiom/actions/runs/38126488372)
(2026-10-11T08:54:51Z), the last full run on exactly this tree.

## 1. Environment

| Item | Value |
|---|---|
| Host | GitHub Actions `ubuntu-latest` |
| Toolchain | `dtolnay/rust-toolchain@stable` (version not pinned) |
| Crate | `axiom 0.1.0`, Rust 2021, zero dependencies |
| Benchmarks | single-threaded, `harness = false` |
| Local device | **not used for builds/tests** (Android/Termux policy) |

Timings below are wall-clock on a shared GitHub-hosted runner and are not
comparable across runner generations. The deterministic work counters
(`candidates`, `derivations`, `conflicts`, `propagations`, fact counts) are the
primary regression signals.

## 2. Build and test result

All 10 CI jobs succeeded. Test totals: **153 passed, 0 failed, 0 ignored**,
plus **1 doc test**. The per-target breakdown is in `AUDIT.md` §3.

```text
cargo test --lib --tests     # 153 passed, 0 failed, 0 ignored
cargo test --doc             # 1 passed
cargo fmt --all -- --check   # clean
cargo clippy --lib --tests -- -D warnings  # clean
cargo build --examples       # clean
cargo test -- --ignored      # 0 ignored; the guard passes
```

CI job wall times (includes toolchain setup, not pure test time):
`test` 11 s, `doc` 19 s, `fmt` 7 s, `clippy` 10 s, `known-defects` 12 s,
`bench-ci` 39 s, `bench-sat` 16 s, `bench-theory` 24 s, `diag` 18 s,
`examples` 8 s.

## 3. Kernel benchmark subset (`cargo bench --bench kernel -- ci`)

Raw rows from the CI log. `Mops/s` is derived from the harness's nominal op
count and must not be compared across different row shapes.

| Benchmark | iters | wall ms | allocs/it | rss kB* |
|---|---:|---:|---:|---:|
| `hash_cons_1000_terms` | 1 | 1.14 | 8,095 | 2,712 |
| `hash_cons_sharing` | 1 | 0.02 | 43 | 2,712 |
| `unify_ground_pairs` | 533 | 50.05 | 6 | 3,200 |
| `match_pattern_vs_fact` | 1,647 | 50.01 | 4 | 3,200 |
| `occurs_check_cost` | 456 | 50.10 | 4 | 3,200 |
| `db_index_lookup` | 22 | 51.25 | 0 | 12,304 |
| `db_index_lookup_arg1` | 22 | 50.07 | 0 | 12,304 |
| `db_scan_lookup` | 1 | 759.13 | 21 | 12,304 |
| `semi_naive_vs_fixpoint_n600[A]` | 3 | 856.76 | 555,459 | 55,928 |
| `semi_naive_vs_fixpoint_n600[B]` | 3 | 821.63 | 554,844 | 56,016 |
| `tc_path_n200` | 1 | 19.24 | 64,750 | 23,536 |
| `tc_path_n1000` | 1 | 984.03 | 1,526,892 | 6,148* |
| `tc_random_n1500` | 1 | 13,997.92 | 6,793,750 | 16,492* |
| `stratified_negation_5000` | 1 | 8.86 | 65,311 | 16,540 |
| `proof_verify_strong` | 1,438 | 50.02 | 805 | 16,576 |
| `proof_verify_shallow` | 2,000 | 0.07 | 0 | 16,576 |
| `memory_per_fact_probe` | 1 | 550.14 | 525,855 | 62,728* |
| `parse_program` | 685 | 50.06 | 1,361 | 62,728 |
| `end_to_end_prove` | 12 | 52.51 | 17,851 | 62,732 |

\* **The `rss kB` column is sampled after the closure returns and the solver is
dropped** (`src/bench.rs:206-258`; F-03). It is post-solve residency, not peak.
Rows with a large derived model (`tc_path_n1000`, `tc_random_n1500`) are
therefore obviously understated. Do not use this column as a memory baseline.
Use `memory_per_fact_probe`'s in-closure print instead:

| Mode | Facts | RSS | Measured | IR payload | Deriv + DB |
|---|---:|---:|---:|---:|---:|
| proofs on | 501,500 | 158,560 kB | 324 B/fact | 20 B/fact | 89 B/fact |
| proofs off | 501,500 | 96,516 kB | 197 B/fact | 20 B/fact | 30 B/fact |

Index selectivity (tuple counts, not timings): 50,000 tuples over 500 distinct
first arguments; scan examines 2.31 × 10⁹ tuples, first-argument index
4.67 × 10⁶, ratio 495.8×; second-argument index measured on the same fixture.

### I1 scaling probe (`cargo bench --bench kernel -- diag`)

| n | facts | rounds | derivations | candidates | ms |
|---:|---:|---:|---:|---:|---:|
| 100 | 5,150 | 2 | 5,050 | 9,900 | 5.1 |
| 200 | 20,300 | 2 | 20,100 | 39,800 | 20.1 |
| 400 | 80,600 | 2 | 80,200 | 159,600 | 87.0 |
| 800 | 321,200 | 2 | 320,400 | 639,200 | 408.8 |

`candidates` grows 4.02× per doubling of `n` (slope ≈ 2.00), and `unbound=0`
at every size. This confirms the second index level is being used and the old
cubic scan is gone.

## 4. SAT corpus (`cargo bench --bench sat`)

Frozen corpus is 9/9 solved; every label is asserted and every certificate is
checked (`tests/sat.rs`).

| Instance | Expected | wall ms | decisions | conflicts | propagations | learned |
|---|---|---:|---:|---:|---:|---:|
| `sat_trivial` | SAT | 0.00 | 0 | 0 | 1 | 0 |
| `unsat_units` | UNSAT | 0.00 | 0 | 0 | 0 | 0 |
| `sat_xor2` | SAT | 0.00 | 1 | 0 | 3 | 0 |
| `unsat_xor01` | UNSAT | 0.01 | 1 | 2 | 2 | 1 |
| `unsat_php32` | UNSAT | 0.01 | 1 | 2 | 9 | 1 |
| `sat_chain7` | SAT | 0.01 | 0 | 0 | 7 | 0 |
| `unsat_php43` | UNSAT | 0.04 | 5 | 6 | 44 | 5 |
| `sat_planted50` | SAT | 0.09 | 10 | 3 | 92 | 3 |
| `sat_planted100` | SAT | 0.89 | 122 | 90 | 2,189 | 90 |

No restarts or deletions occurred on this corpus. That does not exercise the
restart/deletion paths; those are covered by unit tests, not by these
instances.

## 5. Theory benchmark (`cargo bench --bench theory`)

| Benchmark | wall ms | allocs | alloc B/op |
|---|---:|---:|---:|
| `rdl_chain_unsat` | 0.50 | 1,800 | 139,852 |
| `rdl_chain_sat` | 163.82 | 1,113,159 | 666,998,172 |
| `uf_cong_propagate` | 0.24 | 1,613 | 112,756 |

The `rdl_chain_sat` allocation figure is a warning, not a target: 667 MB for
51 difference constraints indicates the theory driver rebuilds too much state
per assignment (F-04). Correctness is asserted and certificates verify; the
cost is the issue.

## 6. Reproduce

From a clean checkout of `4c60f3f` on a normal Linux host:

```sh
cargo test --lib --tests
cargo test --doc
cargo fmt --all -- --check
cargo clippy --lib --tests -- -D warnings
cargo build --examples

cargo bench --bench kernel -- ci
cargo bench --bench kernel -- diag
cargo bench --bench sat
cargo bench --bench theory
```

On this phone, do not run these; push a branch/PR and let `axiom CI` run them.
The GitHub workflow is `.github/workflows/ci.yml`.

## 7. Baseline caveats

1. Per-row RSS is invalid (F-03). Use the in-closure `memory_per_fact_probe`
   numbers.
2. Timing noise on shared runners is significant; treat ±10–20% as noise and
   prefer deterministic counters.
3. The kernel `Mops/s` column is a derived nominal rate, not a universal
   throughput measure.
4. `saturate_naive` and semi-naive now produce the same closure on the tested
   program (`naive_and_semi_naive_agree_on_transitive_closure`), but the A/B
   timing rows are not a proof of algorithmic superiority on all graphs.
5. `rdl_chain_sat` is a stress case for allocation, not representative of
   typical theory use.
6. No external solver was used as an oracle in this baseline. All comparisons
   are internal.

## 8. Checkpoint

* Known-good tree: `4c60f3f`, tag `v4-baseline`.
* v4 work branch: `v4`.
* No source file was modified to produce this baseline; only `docs/v4/` was
  added. The source tree remains byte-identical to `4c60f3f`.
