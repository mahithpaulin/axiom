# Axiom v4 — Stage 0 audit

Audit date: 2026-10-21
Baseline: `main` @ `4c60f3f` (2026-10-11), tagged `v4-baseline`
Working branch: `v4`, branched from `4c60f3f`

This document records what exists, what was verified, and what the evidence does
**not** support. It is the gate for every later v4 stage.

## 1. Method and constraints

* The repository was inspected directly: `git`, the working tree, all remote
  branches, `Cargo.toml`, `src/`, `tests/`, `benches/`, `examples/`, `docs/`,
  and `.github/workflows/`.
* Per the device policy (Android/Termux phone, ~1 GiB free RAM), **no `cargo`
  build, test, or benchmark was run locally**. The authoritative build/test
  evidence is GitHub Actions, which is the project's established verification
  path. The phone was used for reading, diffing, and authoring only.
* The tree at `4c60f3f` is clean and unchanged since 2026-10-11. The CI run
  analysed here (see §3) ran on exactly this commit.
* Claims below cite a file path, a test name, or a CI run/job. Where a claim
  could not be verified, it is marked **unverified** rather than assumed.
* No source was copied from any reference project. Licence obligations for
  Z3, Soufflé, clingo, Vampire, Lean 4, and Fast Downward are recorded in
  [`LICENSE_REVIEW.md`](LICENSE_REVIEW.md).

## 2. Repository snapshot

| Item | Value |
|---|---|
| Remote | `https://github.com/mahithpaulin/axiom` (public) |
| Default branch | `main` |
| Baseline commit | `4c60f3fc1197f44028acf789a4794c5b886e2894` |
| Commit date | 2026-10-11 14:24:49 +0530 |
| Last merge | PR #13, `youtube-verify-fix` |
| Working tree | clean before the v4 branch |
| Licence metadata | `Cargo.toml` says `MIT OR Apache-2.0`; **no `LICENSE*` file exists** |
| Crate shape | one crate (`axiom`), zero external dependencies |
| Size | 12,092 source LOC across 29 modules; 2,362 test LOC |
| Branches | `main`, `base`, `v2`, `v2-play`, `v2.5`, `v2.5-exp`, `thorough-eval`, `v3-slice-1`, `ai-supervisor-system`, `demo-parallel`, `youtube-publish`, `youtube-verify-fix` |
| Tags | `v2.5` (plus this audit's local `v4-baseline`) |

`Cargo.toml` declares one library plus four `harness = false` benches:
`kernel`, `sat`, `theory`, `v2perf`. `Cargo.lock` is gitignored.

## 3. Build and test baseline

The last full `axiom CI` run on `main` is run
[`38126488372`](https://github.com/mahithpaulin/axiom/actions/runs/38126488372)
(2026-10-11T08:54:51Z). **All 10 jobs succeeded.** The tree is identical to the
audit baseline, so this is valid Stage 0 evidence.

| Job | Result | Job wall time |
|---|---|---|
| `test` | success | 11 s |
| `doc` | success | 19 s |
| `fmt` | success | 7 s |
| `clippy` (`-D warnings`) | success | 10 s |
| `known-defects` (`--ignored`) | success | 12 s |
| `bench-ci` (`kernel -- ci`) | success | 39 s |
| `bench-sat` (frozen corpus) | success | 16 s |
| `bench-theory` (DPLL(T)) | success | 24 s |
| `diag` (I1 scaling probe) | success | 18 s |
| `examples` (build) | success | 8 s |

Test totals from the `test` job:

| Target | Passed | Failed | Ignored |
|---|---:|---:|---:|
| lib (`src/`) | 64 | 0 | 0 |
| `tests/chess_play.rs` | 7 | 0 | 0 |
| `tests/determinism.rs` | 5 | 0 | 0 |
| `tests/equivalence.rs` | 4 | 0 | 0 |
| `tests/reference.rs` | 0 | 0 | 0 |
| `tests/robustness.rs` | 16 | 0 | 0 |
| `tests/sat.rs` | 7 | 0 | 0 |
| `tests/soundness.rs` | 18 | 0 | 0 |
| `tests/theory.rs` | 7 | 0 | 0 |
| `tests/v2.rs` | 25 | 0 | 0 |
| **Total** | **153** | **0** | **0** |
| Doc tests | 1 | 0 | 0 |

`tests/reference.rs` is a shared module (`mod reference` in
`tests/soundness.rs`), not a standalone suite; its 0-test target is expected,
not a failure.

The CI does **not** pin a Rust version (`dtolnay/rust-toolchain@stable`), and
does **not** test the declared MSRV (`rust-version = "1.75"`). This is recorded
as finding F-14.

## 4. Verified capability evidence

Detailed status is in [`CAPABILITY_MATRIX.md`](CAPABILITY_MATRIX.md). The
load-bearing evidence:

* **Datalog**: facts, rules, recursion, semi-naive evaluation
  (`src/solver_fwd.rs:438`), two-level indexing (`src/db.rs:41-44`,
  `src/db.rs:128`), stratification (`src/program.rs:28-29`,
  `src/program.rs:115-119`), ground SLD (`src/solver_bwd.rs`), derivation
  proofs (`src/proof.rs`, `src/check.rs`). The `diag` job reports two levels'
  candidate counts growing 4.02× per doubling with **zero unbound scans**,
  i.e. slope 2.00 (`n=100..800`).
* **SAT/CDCL**: two-watched propagation, first-UIP learning, VSIDS, phase
  saving, Luby restarts, learned-clause deletion (`src/sat.rs:11-12`).
  Models are checked by satisfaction (`src/sat.rs:837`); UNSAT is checked by
  RUP (`src/sat.rs:920`). The frozen corpus is 9/9 solved with certificates
  (`tests/sat.rs::frozen_corpus_labels_hold_with_checked_certs`,
  `bench-sat`).
* **SMT fragment (already present, contrary to the old docs)**: integer
  difference logic `x - y ≤ c`, equality/disequality, congruence closure, and
  Nelson–Oppen combination, driven through CDCL(T)
  (`src/theory.rs:1-13`; `tests/theory.rs`, 7 tests). Models are re-checked
  (`verify_theory_sat`) and UNSAT certificates replay every theory lemma
  (`verify_theory_unsat`).
* **Puzzles / CSP**: sudoku, N-queens, map colouring, logic grids
  (`src/puzzle.rs`), propagation with explanations (`src/csp.rs`), independent
  assignment check (`src/csp.rs:123`), 25 V2 tests.
* **Planning**: explicit finite `StateGraph` plus Dijkstra and a bounded
  model-checking lowering to CNF (`src/state.rs:128`, `src/state.rs:209`);
  plan replay (`src/state.rs:110`). This is **not** a PDDL planner.
* **Search**: A*, IDA*, alpha-beta over explicit graphs/trees
  (`src/search.rs:98,159,334`), with path/line verifiers.
* **Chess**: legal movegen, FEN, perft, mate-in-one, fixed-depth negamax with
  draw rules (`src/chess.rs`, `src/chess_play.rs`); 7 integration tests.
* **Go**: 5×5 liberties/captures/ko and capture-in-one (`src/go.rs`);
  no scoring and no full-board play.
* **Deterministic chooser**: pure feature-based choice, limited to V2
  representations (`src/choose.rs:86`).
* **MCP/TUI**: **absent on `main`**; they exist only on the unmerged
  `v3-slice-1` branch (see `BRANCH_ANALYSIS.md`).
* **ASP, general FOL theorem proving, a Lean-style trusted kernel, and a
  Fast-Downward-style declarative planner**: absent.

## 5. Findings

Severity: **high** = credibility or wrong-answer risk; **medium** = missing
capability or misleading measurement; **low** = hygiene.

### F-01 (high) — The honesty documentation is materially stale

The project says “if README and `KNOWN_LIMITATIONS.md` disagree, believe the
latter.” Both now disagree with the source:

| Stale claim | Location | Contradicting evidence |
|---|---|---|
| “No SMT, no constraint propagators, no symbolic arithmetic, no search…” | `README.md:56-57` | `src/theory.rs`; `src/search.rs`; `src/csp.rs` |
| “Constraints, arithmetic theories, planning, search and strategy selection … not implemented yet” | `src/lib.rs:53` | same |
| “Theory combination, CDCL(T), linear arithmetic, congruence closure — no” | `docs/KNOWN_LIMITATIONS.md:399` | `src/theory.rs:1-13`, `tests/theory.rs`, CI `bench-theory` |
| “CDCL(T) / theory combination … [not implemented]” | `docs/ALGORITHMS.md:175` | same |
| “None of this exists” at the head of Stage 2 | `docs/ROADMAP.md:278` (section intro) | II1 (SAT) and II2a (RDL+UF) are implemented |
| “80 pass, 2 ignored” | `README.md` verification section | 153 pass, 0 ignored (CI run above) |
| `PERFORMANCE.md` referenced from six places | `docs/ROADMAP.md:440` | file does not exist |

**Impact.** The credibility anchor is no longer reliable. A v4 implementer
could re-implement capabilities that already exist, or trust a limitation that
was removed. This is the most important Stage 0 finding.

**Action.** Stage 1 begins with a documentation reconciliation commit: either
update the claims or mark them as historical. The capability matrix becomes
the single source of truth until the narrative docs are rewritten.

### F-02 (high) — `Refuted` is still reachable for incompleteness at B3

`Solver::negatives_hold` refuses to evaluate a negated body literal that is not
ground (`src/solver_fwd.rs:99-116`). This is sound, but it makes the engine
incomplete for stratified Datalog: a goal whose derivation needs the negation
evaluated after another literal binds the variable can be reported as
`Refuted` with a completed-saturation certificate, even though the goal is in
the least model. The example and analysis are in
`docs/KNOWN_LIMITATIONS.md` §B3.

**Impact.** A wrong negative answer is possible in the documented “home”
fragment. The status enum cannot currently distinguish “blocked derivation”
from “derived absent”.

**Action.** v4 Stage 3 must either implement anti-join/tabling evaluation for
negation or qualify every negative answer whose proof touched a blocked
negation as `Unknown`. Add the B3 worked example as a regression test first.

### F-03 (medium) — The benchmark RSS column is still measured after the solve

`Bench::run` and `Bench::run_once` sample `rss_kb()` while building the result
row, after the closure has returned and dropped its solver
(`src/bench.rs:206-258`). The CI table therefore reports post-solve
residency: `tc_path_n1000` shows 6,148 kB for a run that derives ~501k facts,
while the dedicated `memory_per_fact_probe` line shows 158,560 kB with proofs
and 96,516 kB without.

`docs/ROADMAP.md` I3 says this was fixed; `docs/KNOWN_LIMITATIONS.md` §A7
correctly says it is open. The index-lookup loops and blank stub rows *were*
fixed (`benches/kernel.rs:306-335`), so I3 is only partially complete.

**Impact.** Any per-row RSS claim in the benchmark table is invalid. Peak
memory must be taken from `memory_per_fact_probe` (whose numbers are sampled
inside the closure) or from a fixed harness.

**Action.** v4 benchmark harness records `peak_rss_kb()` inside the measured
region; add a self-test that a known allocation is visible in the row.

### F-04 (medium) — Theory solving is single-shot and memory-heavy

`TheoryDriver` is documented as single-shot per formula
(`src/theory.rs:966-975`): no assumptions, no push/pop, no incremental reuse.
The `rdl_chain_sat` benchmark allocates **666,998,172 bytes per operation**
for 51 constraints and takes ~164 ms on the CI runner (`bench-theory`, run
38126488372). `Reasoner::refresh` rebuilds the combination and re-asserts every
term for each assignment (`src/theory.rs:735`).

**Impact.** The fragment is correct for its tests but not ready for
cross-domain use at scale, and not an SMT solver in the usual incremental
sense.

**Action.** Stage 4: add assumptions/push-pop, cache the term index, and
measure before adding theories. Do not claim Z3 parity.

### F-05 (medium) — No SMT-LIB frontend or stable serialisation

The SMT fragment is reachable only through Rust types (`Diff`, `TheoryAtom`,
`TheoryDriver`). `docs/IR_SPEC.md` §10 states that no binary or textual IR dump
exists. There is also no common problem/result serialisation across engines.

**Impact.** Cross-domain reasoning and reproducible external benchmarks are
blocked on adapters, not just solvers. The v4 IR/evidence model (Stage 2) is a
prerequisite for the coordinator.

### F-06 (medium) — No shared solver interface or capability declaration

`src/repr.rs` provides one request/operation enum for the V2 representations,
but Datalog, SAT, theory, search, chess, Go, and CSP each expose unrelated
APIs. There is no `capabilities()`/`solve(problem, budget)`/`verify(...)`
trait, no declared fragment, and no uniform resource/cancellation contract.

**Impact.** A router cannot select engines on evidence, and a coordinator
cannot pass verified results between them. Stage 1 must define the interface
before Stage 10 can exist.

### F-07 (medium) — Planning is an explicit transition graph, not a planner

`StateGraph` stores `Action { name, from, to, cost }` (`src/state.rs:23-32`);
`domains.rs` hardcodes five-state and four-state graphs. There are no
preconditions, effects, objects, or PDDL parsing. `shortest_plan` is Dijkstra
over the compiled graph (`src/state.rs:128`), and `bmc_clauses` is a bounded
SAT lowering. This is useful, but it is not Fast-Downward-style planning.

**Impact.** The v4 planning stage is mostly new work, not an optimization of
the existing module.

### F-08 (medium) — No ASP, FOL prover, or trusted proof kernel

There is no grounding/stable-model engine, no resolution/factoring/
superposition, and no typed kernel with definitional equality. Existing
checkers (derivation replay, RUP, theory-lemma replay, plan/path replay) are
independent and valuable, but they are not a general proof kernel.

**Impact.** Stages 6–8 are greenfield. Do not describe existing evidence
checkers as “formal verification” in the Lean sense.

### F-09 (medium) — Licence declaration is not backed by licence files

`Cargo.toml` and `README.md` declare `MIT OR Apache-2.0`; the repository has no
`LICENSE`, `LICENSE-MIT`, or `LICENSE-APACHE`, and GitHub reports no licence.
Under default copyright, the declaration is not enough to grant rights to
third parties.

**Impact.** External reuse/contribution is legally ambiguous. The reference
projects have compatible permissive licences except Fast Downward (GPL-3.0),
which must not be copied. Full table in `LICENSE_REVIEW.md`.

**Action.** Add the two standard licence texts (owner decision) before any
public v4 release; keep the existing dual-licence intent unless changed.

### F-10 (low) — Unmerged branches hold useful work

* `thorough-eval` (PR #6, draft): 31-test evaluation suite, green, not merged.
* `v3-slice-1` (PR #7, draft): std-only MCP stdio server and a TUI skeleton;
  the TUI adds external crates, the MCP crate depends only on `axiom`.
* `ai-supervisor-system`: superseded by the merged PR #8.
* `demo-parallel`: not part of this project (per project memory).

**Action.** Port the `thorough-eval` tests onto `v4` after the interface is
stable. Salvage the MCP server design, not the TUI dependency tree, into the
v4 ecosystem stage.

### F-11 (low) — CI does not test the MSRV or pin the toolchain

`rust-version = "1.75"` but CI uses `stable`. A future `stable` feature could
break the declared MSRV silently.

**Action.** Add an MSRV job once the v4 workspace exists (or lower the claim).

### F-12 (low) — `Cargo.lock` is gitignored

With zero dependencies this is harmless. A v4 workspace with dependencies
should commit the lockfile for reproducible CI/release builds, or explicitly
document why not.

## 6. What is trustworthy today

* Datalog least-model computation on the positive, finite fragment, including
  the repaired join enumeration and proof replay.
* SAT solving on the frozen corpus with both model and RUP certificates.
* The RDL+UF theory fragment for the cases covered by `tests/theory.rs`,
  including Nelson–Oppen exchange and certificate replay.
* The V2 puzzle/search/chess/Go/plan modules within their documented scope.
* The `Status` discipline for `Proved`/`Refuted`/`Found`/`Impossible` versus
  `Exhausted`/`Unknown`, except for the B3 negation hole (F-02).
* The CI matrix as a regression gate.

## 7. What cannot be concluded from this audit

* **No claim of competitiveness** against Z3, Soufflé, clingo, Vampire, Lean,
  or Fast Downward. No differential benchmark against them was run.
* **No claim of completeness** beyond the tested fragments. In particular,
  stratified negation is incomplete (F-02), and the theory fragment is
  difference logic + congruence only.
* **No local performance numbers.** All timings are GitHub-hosted runners and
  are noisy; deterministic counters are the primary signal.
* **No fuzzing or long-duration soak test.** `tests/robustness.rs` covers
  hostile inputs, but there is no coverage-guided fuzzing.
* **No external proof checking** (e.g. DRAT/drat-trim, Coq/Lean) of the
  existing certificates. The checkers are independent implementations inside
  this crate.

## 8. Baseline recovery

The known-good baseline is recoverable without touching `main`:

```sh
git fetch origin
git checkout v4-baseline      # tag on 4c60f3f
# or
git worktree add ../axiom-baseline 4c60f3f
```

The audit branch is `v4`, created from the same commit. No existing branch,
tag, or file was rewritten or deleted during Stage 0.

## 9. Stage 0 gate

Stage 0 is complete when the five Stage 0 documents exist, the baseline build
and tests are recorded, the capability matrix covers every requested engine
family with evidence, and the licence review is explicit. Those conditions are
met by this document set.

Architectural changes begin in Stage 1. The first Stage 1 commit is a
documentation reconciliation (F-01), because leaving a false “not implemented”
list in place would poison every later capability decision.
