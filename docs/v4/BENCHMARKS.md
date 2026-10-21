# Axiom v4 — benchmarks and measurement

This document separates what is measured, what is only counted, and what is not
measured at all. v4 added engines and verification; it did **not** produce a
competitive performance claim against any external solver.

## 1. Environment

- Authoritative runner: GitHub Actions `ubuntu-latest`, single-threaded jobs.
- Local device: Android/Termux phone. It is used for development checks, but
  CI remains authoritative; see `docs/v4/BASELINE.md` §1.
- Toolchain: `stable` (not pinned). The declared MSRV `1.75` is not exercised by
  CI; this remains an open infrastructure gap.
- Timings are wall-clock on shared runners and are noisy. Deterministic work
  counters are the regression signal.

## 2. Existing benchmark suites

| Suite | Command | What it measures |
|---|---|---|
| Kernel subset | `cargo bench --bench kernel -- ci` | hash-consing, unification, matching, index selectivity, semi-naive, proofs, parse, end-to-end |
| Full kernel | `cargo bench --bench kernel` | all of the above plus larger cases |
| Scaling probe | `cargo bench --bench kernel -- diag` | four `n` values, derivation/candidate counts |
| SAT corpus | `cargo bench --bench sat` | frozen 9-instance CDCL corpus with checked certificates |
| Theory | `cargo bench --bench theory` | RDL unsat/sat and UF congruence propagation |
| V2 | `cargo bench --bench v2perf` | CSP/chess/go/search paths |

CI runs `bench-ci`, `bench-sat`, `bench-theory`, and `diag` on every push to
`v4`; `v2perf` exists but is not part of the v4 CI gates.

## 3. Baseline figures

The Stage 0 baseline is recorded in `docs/v4/BASELINE.md`. Load-bearing numbers:

- index selectivity: 495.8× fewer tuples for a first-argument lookup than a
  scan on the fixture;
- transitive closure: candidate growth slope ≈ 2.00 over `n = 100..800`, with
  `unbound = 0`;
- SAT corpus: 9/9 instances reach their expected labels with certificates;
- memory probe: 324 B/fact with proofs, 197 B/fact without (501,500 facts);
- `rdl_chain_sat` allocates ~667 MB for 51 difference constraints — a known
  allocation problem, not a correctness failure.

These numbers describe the root crate. They are not v4 cross-engine results.

## 4. What v4 measures

v4 gates are correctness and verification gates, not performance rankings:

| Gate | Evidence |
|---|---|
| Workspace unit/integration tests | `cargo test --workspace --lib --tests` |
| Doc examples | `cargo test --workspace --doc` |
| Lints | `cargo clippy --workspace --lib --tests -- -D warnings` |
| Formatting | `cargo fmt --all -- --check` |
| No ignored tests | `known-defects` job |
| Existing kernel/SAT/theory suites | unchanged jobs |
| Examples | `cargo build --examples` |

A small differential correctness round is separate from these gates:

| Harness | Command | Scope |
|---|---|---|
| External differential | `python3 benchmarks/external/run.py --axiom target/release/axiom-bench` | 19 fixtures against Z3, clingo, Soufflé, Fast Downward, and Vampire when installed |

The workflow `.github/workflows/external-bench.yml` is manual and uploads
`results.json` and `results.md`. Round 4 required every oracle and matched all 19
fixtures. A skipped oracle is not agreement, and one fixture per family is not a
conformance or performance result. No v4 engine has a throughput benchmark or
scaling study, and no competitive ranking is claimed.

## 5. RSS defect

`src/bench.rs:206-258` samples RSS **after** the benchmark closure returns and
the solver is dropped. The `rss kB` column in kernel output is therefore
post-solve residency, not peak, and understates rows with large derived models.
This is F-03 in `docs/v4/AUDIT.md` and remains unfixed.

Valid memory evidence is limited to `memory_per_fact_probe`, which prints inside
the closure. Any new memory claim must use an in-closure measurement or a
separate process-level probe.

## 6. Reproducibility rules

- Report deterministic counters (`candidates`, `derivations`, `selected`,
  `generated`, `states`, `expanded`, fact counts) alongside time.
- Never compare `Mops/s` across rows with different nominal op counts.
- Never compare absolute times across runner generations.
- State the budget and structural caps with every v4 result.
- A `ResourceLimit` is not a performance result; it is a stopped run.
- No retries to hide noise; report the run.

## 7. Remaining measurement work

The external harness exists, but these are still not done:

- a broad external differential suite (the current suite has 19 fixtures);
- a cross-engine conformance fixture format;
- performance and scaling comparisons with clingo/Vampire/Fast Downward/Z3;
- peak-RSS instrumentation;
- proof-size and verification-time distributions for the FOL kernel;
- ASP enumeration scaling beyond the 22-atom cap;
- plan-search scaling and a comparison of A* `h_max` against blind BFS.

Until these exist, v4 claims are functional: what each fragment decides, with
what evidence, and where it stops.

## 8. External differential rounds

### Round 1

Run `39596516261` (`external differential benchmarks`, 2026-10-21) used commit
`65ea4db` and the 12-fixture harness. Results:

- 12 cases total;
- 8 matched an independent oracle;
- 0 mismatches;
- 4 skipped because the Ubuntu apt repositories did not provide Soufflé or
  Vampire. The skipped cases were three Datalog and one FOL case.

Matched: two Z3 SAT cases, five clingo ASP cases, and one Fast Downward planning
case. Axiom's answers also matched the declared expected answer in all 12 cases,
including the skipped ones.

This is a functional smoke test, not a conformance or performance result. The
workflow now installs Soufflé 2.5 and Vampire 5.1.0 from pinned upstream release
assets for later rounds.

### Round 2

Run `39597261031` (2026-10-21, commit `a5328e4`) installed pinned Soufflé 2.5
and Vampire 5.1.0 binaries. With `allow_missing_oracles=false`, the run required
every oracle and completed:

- 12 cases total;
- 12 matched an independent oracle;
- 0 mismatches;
- 0 skipped.

The round covers two Z3 SAT cases, five clingo ASP cases, three Soufflé Datalog
cases, one Fast Downward planning case, and one Vampire FOL case. This removes
the round-1 oracle gap but does not turn the suite into a conformance or
performance claim: the fixtures are small and deliberately hand-written.

### Round 3

Run `39601253129` (2026-10-21, commit `8073d13`) added two ground-equality FOL
fixtures and required every oracle:

- 14 cases total;
- 14 matched an independent oracle;
- 0 mismatches;
- 0 skipped.

The FOL cases are `equality-substitution` (`a = b`, `P(a)` therefore `P(b)`) and
`equality-congruence` (`a = b` therefore `f(a) = f(b)`); Vampire reported
`Theorem` for both. The suite remains a small functional differential check, not
a conformance or performance claim.

### Round 4

Run `39607159188` (2026-10-21, commit `95bbd4b`) added five SMT-LIB 2 fixtures
and required every oracle:

- 19 cases total;
- 19 matched an independent oracle;
- 0 mismatches;
- 0 skipped.

The new family is SMT: `difference-sat`, `difference-unsat`, `equality-unsat`,
`congruence-unsat`, and `boolean-sat`. Z3 agreed with Axiom on all five. The
`congruence-unsat` case is the interesting one: `a = b` together with
`f(a) != f(b)` is unsatisfiable only through congruence, and both solvers
found it. This is still five hand-written fixtures, not a conformance suite.
