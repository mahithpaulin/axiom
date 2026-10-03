# ROADMAP

Ordered next steps. Two sections: **Immediate** — work that must happen before
anything else is credible — and **Stage 2** — capability, in dependency order.

Every entry states why it is next, what it depends on, what "done" means, and how
it will be benchmarked. Benchmarks are bounded by step budgets and report
deterministic work counters alongside timings (DD-0016); a wall-clock cutoff is
never used as a limit.

Nothing in Stage 2 is implemented. Entries are deliberately conditional on the
Immediate section being complete: building new solvers on top of a kernel with a
known wrong `Refuted`, a wrong baseline, and benchmarks that measure nothing
would produce numbers nobody could interpret.

---

## IMMEDIATE

### I1. Find and fix the unbound-scan root cause — FIXED (second index level)

**Verified.** `diag` post-fix: candidates 9,900 / 39,800 / 159,600 / 639,200
for n ∈ {100, 200, 400, 800} — ratios 4.02× per doubling, slope 2.00 — with
unbound scans at **zero** at every size (was 51B offered unbound at n=800).
`derivations` and `rounds` unchanged (2 rounds, exact closures). Random graph
(`tc_random_n1500`) completes in ~15 s in the CI bench. Locked by
`tests/soundness.rs::transitive_closure_scales_quadratically_not_cubically`,
which fits the slope over three sizes and asserts 1.5 < slope < 2.5.

**The problem.** On a path graph, `candidates` grows as `≈ 0.5·n³` where
`0.5·n²` is correct. At n = 800, instrumentation counted ≈ 2.92 × 10⁸ UNBOUND
(non-indexed) scans against ≈ 4.27 × 10⁵ bound index lookups. The cause is not
established. Full statement, including what has been ruled out, in
`docs/KNOWN_LIMITATIONS.md` §C1.

**Reproduce.**

```sh
cargo bench --bench kernel -- diag
```

`scaling_diagnostic` (`benches/kernel.rs:513-532`) prints, for
n ∈ {100, 200, 400, 800}: `facts`, `rounds`, `derivations`, `candidates`, `ms`.
`facts` should be `n(n+1)/2 + n` — the `path` closure plus the `n` `edge` facts,
which count as IDB per DD-0017. `candidates` is the column that is wrong. Fit
`log(candidates)` against `log(n)`: the slope is currently ≈ 3.

**Step 1 — instrument, do not guess.** Done: `Solver::scan_attr` counts tuples
examined by `(rule, body position)` split into bound vs unbound
(`src/solver_fwd.rs`, `src/solver.rs::scan_attribution`), and `diag` prints
the worst unbound contributors per n. Run it before theorising. The two
obvious candidates were already checked and are *not* it: `first_bound` looks
only at argument 0 and only at ground values (fixed), and a wrong index key
reduces scans rather than inflating them (`src/db.rs:109-127`).

**Step 2 — fix.** Step 1 showed it: the recursive rule fired at the edge
position leaves `path(X, Y)` with nothing bound, so every edge-seeded firing
scans all of `path` (51B tuples offered unbound at n=800 against 639k bound).
The position that *is* bound there is argument 1 (`Y`), which no level
indexed — hence the second index level (`by_second`, position-tagged
`(pos, key)` lookups). Dropping the edge-seeded firing instead would be
unsound: new edge facts must propagate through it.

**Done means.** `candidates` for path-graph transitive closure fits
`0.5·n²` (slope ≈ 2 on a `log`/`log` fit across n ∈ {200 … 5000}), confirmed on
both the path graph and a random graph, with the semi-naive counters for
`derivations` and `rounds` unchanged. `tc_path_n*` in the scaling table
(`benches/kernel.rs:536-577`) becomes the regression check.

**Benchmarked by.** `cargo bench --bench kernel -- diag`, plus the `scaling:`
table's `candidates` column, plus a new `unbound_scan_ratio` row in the indexing
section.

---

### I2. Fix or delete `saturate_naive`

**The problem.** `Solver::saturate_naive` (`src/solver_fwd.rs:436-465`) derives
≈ 1 200 facts where ≈ 180 900 are correct on the n = 600 path graph. It is
retained only as the baseline for `semi_naive_vs_fixpoint_n600`
(`benches/kernel.rs:301-314`), and its output is not the least model.
`docs/KNOWN_LIMITATIONS.md` §A6.

**Options, in order of preference.**

1. Fix it. The naive loop's only real difference from `saturate` is that it
   re-evaluates every rule every round with no delta; the failure to enumerate
   all solutions per firing is a caller-side bug, so port the resumable loop.
2. Replace it with the obviously-correct string-based fixpoint already written in
   `tests/reference.rs::least_model`. A baseline does not need to be fast, and
   that one is correct by inspection.
3. Delete it, and re-baseline the semi-naive comparison against a corrected
   variant.

**Done means.** `saturate_naive` and `saturate` return the same `idb_facts` and
the same rendered closure set on the same program, asserted in a test — not
just compared in a benchmark. (Same `closure_hash` is unachievable by design:
the hash sums arena node ids, and two engines intern derived facts in different
orders. The hash is order-independent within one arena lineage only.) That
single assertion would have caught this the first time it ran. Locked by
`tests/soundness.rs::naive_and_semi_naive_agree_on_transitive_closure`.

**Root cause.** The resumable join kept one cursor per depth across solutions,
but an inner level's candidate list changes identity when outer bindings move
to a different index bucket. Resuming the stale cursor skipped the bucket's
contents, so unseeded multi-level joins derived ~1 fact and stopped. **Fix:**
truncate the cursor/mark stacks on every advancing match
(`src/solver_fwd.rs`), so re-descent restarts inner levels from zero with
current bindings — textbook nested-loop semantics.

**Benchmarked by.** `semi_naive_vs_fixpoint_n600[A|B]`, which is currently
uninterpretable and can only be filled in after this. The A/B rows must be
accompanied by the fact count from both modes; identical counts are the
correctness check, the timings are the performance check.

---

### I3. Fix the invalid benchmarks and the RSS measurement

Three defects, all in `src/bench.rs` and `benches/kernel.rs`, all detailed in
`docs/KNOWN_LIMITATIONS.md` §A7.

* **`db_index_lookup` and `db_scan_lookup` measure nothing** (`benches/kernel.rs:277-291`).
  Both call `db.candidates(pred, …).len()` — `slice::len` is O(1). Fix by
  consuming the returned tuples (accumulate `black_box(t)` over the slice) so
  the loop cost is proportional to the number of candidates returned. The
  selectivity ratios printed just above them are counts, not timings, and the
  row labels should say so.
* **`rss_kb` is sampled after the solver is dropped** (`src/bench.rs:236`,
  `src/bench.rs:258`). Every memory-sensitive closure builds and drops its
  `Solver` inside `f`. Switch the `rss_kb` column to `peak_rss_kb()`
  (`VmHWM`, `src/bench.rs:85`), which is already implemented and currently only
  passed to `black_box`. Sampling peak from inside the timed region is the
  alternative and is strictly more comparable across runs.
* **The summary prints a blank row per measurement.** `Bench::push` ignores its
  argument (`src/bench.rs:209`) and every caller pushes a `Row::default_stub()`
  after the real row (`src/bench.rs:239`, `262`, `290`). Delete the stubs.

**Done means.** `db_index_lookup` shows the index and `db_scan_lookup` the scan
with a ratio consistent with the 495.8× of DD-0006, in time and not just in
tuple counts; the `rss kB` column for `memory_per_fact_probe` is ≥ the figure
DD-0014 reports; and `b.report()` prints exactly one row per benchmark.

**Benchmarked by.** Itself. This is a prerequisite for trusting every other
number in the suite.

---

### I4. Compile and green the four integration suites in `tests/`

**The problem.** `tests/soundness.rs` (290 lines), `tests/determinism.rs` (121),
`tests/robustness.rs` (298) and `tests/reference.rs` (251) are written and have
never been compiled. Nothing in `git log` touches `tests/` except one commit
that capped a pathological benchmark, and no CI configuration exists. Several of
the engine's most load-bearing invariants are asserted *only* in these files:

| Claim | Asserted in |
|---|---|
| rule-local variable namespacing | `soundness.rs` via `mod reference`; `program.rs` unit test |
| derivations re-verify independently | `soundness.rs::every_derived_fact_has_a_verifiable_proof` |
| a tampered proof is rejected | `soundness.rs::a_tampered_proof_is_rejected` |
| `Refuted` requires a closure certificate | `soundness.rs::refutation_requires_a_closure_certificate` |
| `Exhausted` is never `Refuted` | `soundness.rs::an_exhausted_search_is_never_reported_as_refuted` |
| no non-ground head is ever stored | `soundness.rs::no_bindings_survive_saturation` |
| `ProofMode::Off` downgrades honestly | `soundness.rs::proof_mode_off_downgrades_the_status_honestly` |
| agreement with a naive reference | `soundness.rs::agrees_with_naive_reference_on_random_programs` |
| run-to-run determinism of closure, counters, proofs | `determinism.rs` (5 tests) |
| hostile input returns, never panics | `robustness.rs` (13 tests) |

**Known compile failure.** `tests/robustness.rs:8` imports
`axiom::{exterior, Budget, Exhausted, Limits, Solver, Status}`. `Limits` is
defined at `src/exterior.rs:34` and is **not** re-exported at the crate root —
`src/lib.rs:97-106` re-exports `Budget`, `Db`, `Subst`, `SymbolTable`,
`TermStore`, `program::*`, `proof::*`, `solver::*`, `status::{Exhausted,
Status}` and `TermId`, and nothing else. `axiom::Limits` does not exist, so this
target cannot build. Either add `pub use exterior::Limits;` or import
`axiom::exterior::Limits`.

**Also check while compiling.** `src/exterior.rs:27` cites `tests/malformed.rs`,
which does not exist; the malformed-input tests are in
`tests/robustness.rs::malformed_programs_are_rejected_without_panicking`. Fix
the reference rather than the file.

**Then expect real failures.** Once the targets build, the suites will exercise
code paths no test has run. In particular
`soundness.rs::refutation_requires_a_closure_certificate` calls
`solver.verify(&proof)` on a `Refuted` outcome, which returns
`Err(CheckErr::Unsupported)` because `Solver::verify` never looks at
`proof.saturation` (`docs/KNOWN_LIMITATIONS.md` §A3). That failure is correct
and is the specification for I5.

**Done means.** `cargo test` compiles all four targets, all pass, and CI runs
`cargo test` plus `cargo bench --bench kernel -- diag` on every change. Until
there is CI, "never been compiled" is a permanent hazard, not a historical fact.

**Benchmarked by.** It is not a benchmark. It is the precondition for believing
any benchmark.

---

### I5. Close the correctness risks (do together with I4)

Not in the original brief; it belongs here because I4 will surface it and because
it is cheap while the code is open. Items A1–A5 in
`docs/KNOWN_LIMITATIONS.md`:

* **A1** — `prove` returns an unsound `Refuted` when a candidate rule was
  skipped by both engines (a `backward_only` rule with a negated body literal, a
  non-ground subgoal, or the depth bound). Fix: distinguish "declined" from
  "failed", and refuse `Refuted` when `rules_by_pred[pred]` contains any
  `backward_only` rule. Use `Status::Unknown`, which already exists.
* **A3** — wire `proof.saturation` into `Solver::verify`.
* **A5** — after A1, `Status::Unknown` is actually reachable, and the prose in
  `src/lib.rs:41-44`, `docs/ARCHITECTURE.md:159-162` and
  `src/solver_bwd.rs:22-24` becomes true instead of aspirational.
  `Status::Impossible` and `Exhausted::Depth` remain unconstructed; either use
  them or document them as reserved.

**Done means.** Every test in I4 that asserts on a negative answer also asserts
that the negative answer was *earned*. Add a regression test using the two
programs in `docs/KNOWN_LIMITATIONS.md` §A1, asserting `Unknown`, not `Refuted`.

**Benchmarked by.** `refutation_is_never_unearned` — a new benchmark row that
runs the §A1 programs and asserts the status, so the property is checked by the
suite that runs in CI, not only by a unit test.

---

## Stage 2, in dependency order

**None of this exists.** The list is ordered strictly by dependency: each item
assumes the previous one is finished, measured and green. `docs/ALGORITHMS.md`
§8 is the corresponding "not implemented" list.

### II1. CDCL SAT core

**Why next.** Highest capability per line of anything on the list. It is also
the substrate for everything after it: theory combination, propagators, and the
state-space lowering all consume a clause store and a conflict analysis.

**Depends on.** I1–I5. Architecturally it depends on nothing — it lowers the IR
into its own flat literal array, per DD-0001: the IR is the interchange format,
not the executable form.

**Scope.** A clause database, two-watched literals, 1UIP learning, VSIDS,
phase saving, restarts, and clause deletion. Input is the `Program`'s ground
instances only at first; no decision heuristics from elsewhere.

**Done means.** For CNF inputs, `Proved` for satisfiable instances carries a
DRAT-format or resolution-format certificate that an independent checker (a new
`check::` module, per DD-0010 — it must not share code with the solver) accepts.
`Refuted` for unsatisfiable inputs carries the conflict. Benchmark instances
that exceed the budget return `Exhausted`, never `Unknown` and never `Refuted`.

**Benchmarked by.** A frozen CNF corpus (DIMACS-style files checked into
`benches/data/`) with published satisfiable/unsatisfiable labels; report solved
count at a fixed step budget, plus `conflicts`, `decisions`, `propagations`,
`learned_clauses`. Every run must record which instance and which budget, so two
runs are comparable.

---

### II2. CDCL(T): linear arithmetic and congruence closure

**Why next.** Theory combination is what turns a SAT core into an SMT solver,
and it is the natural home for the arithmetic that Stage 1 cannot express at all
(`docs/KNOWN_LIMITATIONS.md` §B7).

**Depends on.** II1. There is no point writing theory propagators before there
is a conflict analysis to hand them to.

**Scope.** Simplex for linear real and integer arithmetic; Nelson–Oppen or an
E-matching + congruence closure combination; `T`-implication recording so theory
conflicts become learnable clauses.

**Done means.** Theory propagation produces *implications*, not just failures —
a theory that removes a literal must record why, or the learned clause is
unsound. Every theory conflict is replayable by the independent checker.

**Benchmarked by.** QF_LIA / QF_LIA-UF families, solved count at fixed budget
plus `theory_conflicts` and `arith_lemmas`. Cross-checked against the
naive-reference discipline of `tests/reference.rs`: a brute-force model-satisfies
the same formula over a small finite domain and the two must agree on
satisfiability for every instance small enough to enumerate.

---

### II3. Constraint propagators, with explanations

**Why next.** It is the family the charter §12 names, and it is where the
project's proof obligation bites hardest.

**Depends on.** II1 (and ideally II2 for mixed discrete/continuous domains).

**Scope.** Domains, propagators, MAC search. **Every propagator that removes a
value must record the reason as an explanation.** This is not optional and not a
refinement: a propagator that prunes a value without recording why cannot
support a proof, so the solver would be forced to report `Found` for everything
and the checker would have nothing to check.

**Done means.** A propagator is admissible into the engine only if it produces
explanations; the trait signature should make a propagation without one a compile
error rather than a runtime surprise. `Impossible` — a status that exists and is
never constructed — becomes reachable here and should carry the same certificate
discipline as `Refuted`.

**Benchmarked by.** MiniZinc-style or hand-written scheduling/allocation
instances; propagation count, nodes, and MAC failures at a fixed budget, plus
solved count. Memory per domain domain reported, because dense bitsets and a
hash-consed DAG have very different costs (DD-0001).

---

### II4. State-space lowering onto the clause IR

**Why next.** This is the generality test with teeth. The exterior already knows
how to lower a state-transition system into rules (`docs/ARCHITECTURE.md` §2);
the missing piece is a lowering onto the *clause* IR, so that planning problems
and turn-based games are solved by the SAT engine rather than by bottom-up
Datalog — which cannot represent them, because a plan of unbounded length is not
a least fixed point of a finite relation.

**Depends on.** II1. Logically it also benefits from II3 for resource-constrained
planning.

**Scope.** `state(s)`, `action(a, s, s')`, and `goal(s)` compiled to clauses;
reachability as bounded model checking, with the bound an explicit parameter of
the `Status` rather than an assumption. Game trees as the same structure with
minimax quantifiers over the clause level.

**Done means.** The generality claim in `docs/ARCHITECTURE.md` §8 is extended
with two new rows in that table, each requiring *zero* changes to the core
engines — only an adapter. That is the actual acceptance criterion. If a core
change is needed, the lowering is in the wrong place.

**Benchmarked by.** Gripper, blocksworld and Logistics instances; nodes expanded,
and proved-optimal or proved-infeasible counts at a fixed budget, all with the
step budget recorded. Optimality claims must carry a certificate, which means a
lower-bound argument checkable by the independent checker.

---

### II5. Search

**Why next.** After II4, because games and planning are the problem families
search is *for*. Doing search before a state-space lowering would mean choosing
what to search over first, arbitrarily.

**Depends on.** II4.

**Scope.** IDA*, A*, alpha-beta, transposition tables. Uniform-cost and informed
search over an explicit state graph, sharing the state lowering from II4 rather
than inventing a second representation.

**Done means.** A `Proved` answer for a game is a game-tree certificate the
checker replays; an optimality claim carries both the solution and the bound
that excludes everything cheaper.

**Benchmarked by.** The II4 instance families plus game positions; nodes
expanded, terminal evaluations, transposition hit rate, and solutions found per
second at a fixed node budget.

---

### II6. Strategy selection

**Why next.** Literally last among the solvers, and it is pointless with one
engine (DD-0007's reasoning about not depending on an external prover applies
here too: a portfolio that is one entry is not a portfolio).

**Depends on.** II1–II5 all existing and measured. The precondition is that each
solver has a *measured* region where it wins, from the benchmarks above.

**Scope.** A deterministic chooser: given a problem's measured features, pick an
engine. Determinism is a hard requirement — `tests/determinism.rs` pins it and
`closure_hash` (`src/solver.rs:232-242`) is order-independent precisely so that
the same problem must give the same answer regardless of which engine ran.

**Done means.** Selection is a pure function of the input features, asserted by
a determinism test. It never changes an answer, only which engine produced it —
and every answer still carries its own proof.

**Benchmarked by.** Per-instance engine win/loss matrix over the frozen corpora
from II1, II2, II3 and II5, plus the geometric-mean speedup of the portfolio
over the best single engine. A portfolio that does not beat the best single
engine on the geometric mean does not ship.

---

### II7. Compiler passes

**Why next.** Last. They optimise what already exists, and optimising a kernel
with an unexplained `0.5·n³` and a wrong baseline would be optimising the wrong
thing.

**Depends on.** II1–II6 for the full set; individual passes can land earlier.

**Scope.** The charter's §9 passes. Currently only constant folding and
dead-static-rule elimination exist (`docs/ALGORITHMS.md` §8). Missing: rule
subsumption, argument reordering by selectivity, join reordering, magic sets,
semi-naive variant selection (all-old vs all-new vs mixed, currently fixed to
mixed), partial evaluation, and stratification minimisation.

**Done means.** Each pass is individually switchable and individually
measurable. A pass that does not reduce `candidates`, `rounds` or bytes-per-fact
on its own benchmark is removed, not kept for tidiness.

**Benchmarked by.** Every pass gets an A/B row via the existing
`Bench::compare`, which already exists for exactly this
(`src/bench.rs:266-292`). Report the deterministic counters first: a pass that
moves `candidates` changed the algorithm; a pass that only moves wall time moved
a constant factor, and the report must say which.

---

## Triggers to revisit existing decisions

Decisions are not permanent. Each carries the measurement that would reopen it.
The point of recording the trigger is that nobody has to guess when it fired.

### DD-0005 — path compression in the substitution: currently **off**

**Decision.** No path compression. Union by rank bounds variable-only chains at
O(log n); compression rewrites would all have to be trailed for undo, inflating
both the trail and the undo cost.

**Status of the evidence.** Unfinished, and the source comments overstate it.
`docs/DESIGN_DECISIONS.md:104-105` says plainly: *"Stated expectation, not yet
measured end-to-end. Recorded as unfinished rather than dressed up as a result."*
But `src/subst.rs:28` claims *"Measured both ways; see DD-0011"* — and DD-0011 is
about the resumable join, not about compression. One of the two is wrong. Until
it is measured, the source comment is the incorrect one.

**Trigger.** Measure `find` call cost as a share of total run time on a workload
with long substitution chains — candidate families: the I4 deep-recursion cases,
and II1's clause learning, where every conflict clause is a substitution over
shared literals. Revise if `find` exceeds ~10% of run time *and* trailing the
rewrites costs less than the chains it removes. Until then: leave it off. The
type parameter that keeps the experiment honest already exists.

### DD-0006 — index depth: currently **two levels (positions 0 and 1)**

**Decision.** A per-predicate vector plus first- and second-argument hash
indexes. The second level fired its own trigger: I1's attribution showed
edge-seeded transitive-closure steps scanning `path(X, Y)` with only argument
1 bound, so the one-level index was provably unused there — not "the same bug
twice" (the caveat below is discharged).

**Measured so far.** 50 000 tuples over 500 distinct first arguments: a scan
examines 2.31 × 10⁹ tuples, the index 4.67 × 10⁶ — 495.8× fewer, or 92.4 tuples
per lookup instead of 50 000. Note these are *tuple counts*, computed via
`.len()`; the timing rows that were supposed to accompany them measure nothing
(`docs/KNOWN_LIMITATIONS.md` §A7, fixed by I3).

**Trigger.** Any benchmark family in which arguments 0 *and* 1 both have low
selectivity while a later argument (position 2+) is highly selective. The old
trigger — a selective non-leading argument with only a first-argument index —
fired for I1 and is discharged. The caveat stands in its new form: if neither
indexed level is being *used* on some future workload, adding a third measures
the same bug twice.

### Also open

* **DD-0012 — no `resolve` memoisation.** Revise if `resolve` exceeds ~20% of run
  time on a traversal-heavy workload, measured as such. A `ResolveCache` type
  already existed and was deleted; reintroducing it needs a number.
* **DD-0017 — `pred_idb` includes fact-only predicates.** Accepted, documented,
  not a bug. Revisit only if it causes a measurable cost: it makes `edge`
  contribute to `idb_facts` and puts extensional predicates in the delta, which
  is visible in every benchmark number involving `idb_fact_count`.
* **DD-0015 — monolith, not a workspace.** Trigger: compile time exceeding ~60 s
  on the 2-core box, or a genuine module cycle that needs naming.
* **DD-0007 — zero dependencies.** Revisit if a capability appears that cannot be
  built correctly from scratch and would otherwise be *imported*. As oracles in
  tests, never in the shipped reasoning path.

---

## Things deliberately not planned

Stated so they are not mistaken for gaps someone forgot to schedule.

* **No GPU path.** Every representation choice in the engine is a scalar `u32`
  node index and a linear scan; a GPU changes none of the dominant costs, and
  determinism on the CPU is what makes the proof certificates checkable at all.
* **No neural components.** DD-0013: on a single core a neural forward pass
  costs more than the symbolic heuristic it would replace, and that heuristic has
  to be verified anyway. Revisit only when a symbolic heuristic is *measured* to
  underperform on a specific family and a neural alternative beats it
  reproducibly.
* **No dependency on an existing prover.** DD-0007: pulling in Z3 or a
  first-order prover would make the demonstrated capability somebody else's, and
  the engine a black box. External solvers belong as test oracles only, which is
  exactly what `tests/reference.rs` already is — stronger evidence here than Z3,
  because it cannot share a bug.
* **No partial answer that is not representable in `Status`.** Adding an
  "incomplete but probably right" flag, or a confidence score, would undo the
  single design decision the whole status enum exists to make. Unknown is
  honest; almost-certain is not.
* **No pretence of generality beyond the fragment.** `docs/ARCHITECTURE.md` §10 and
  `docs/KNOWN_LIMITATIONS.md` state the ceiling. Advertising above it is the one
  failure mode this roadmap cannot engineer away.

---

## Related documents

| Document | Contents |
|---|---|
| `docs/ARCHITECTURE.md` | layers, module map, data flow, status contract, generality test |
| `docs/IR_SPEC.md` | the IR, normative; §10 covers the missing serialisation |
| `docs/ALGORITHMS.md` | what each algorithm implements and where it stops being correct; §8 is the "not implemented" list |
| `docs/DESIGN_DECISIONS.md` | hypothesis → alternatives → measurement → decision; numbering is stable, do not renumber |
| `docs/KNOWN_LIMITATIONS.md` | itemised limitations, with correctness risks at the top |
| `docs/LANGUAGE_SPEC.md` | the exterior's surface syntax, tokeniser, limits, every error message |
| `docs/PERFORMANCE.md` | **missing.** Referenced from `src/solver.rs:42`, `src/term.rs:247`, `src/subst.rs:68`, `src/budget.rs:11`, `docs/ARCHITECTURE.md:210` and `docs/ALGORITHMS.md:157`, and it does not exist. Every measurement cited in this roadmap should land there, including the I1 counters. |
| `README.md` | crate status, the honesty contract, verification. |
---

## Open defects, numbered as referenced by the test suite

These were `#[ignore]`d or failing tests, not hypotheticals. I1, I2, I5 and I6
are fixed (root cause and fix recorded below); the suite is green with no
exclusions. I7, I8 remain open. I3's measurement defects are fixed; I4
(compiling the suites + CI) is done.

### I1 — Unbound scans dominate the join (highest priority)

**Measured:** `candidates ≈ 0.5·n³` for transitive closure on a path graph, where
the correct figure is `0.5·n²`. Instrumented at n=800: **292 075 000 unbound
(non-indexed) scans** against **427 250 bound index lookups** (1 candidate each —
the index itself works perfectly).

**Reproduce:** `cargo bench --bench kernel -- diag`

**Status:** root cause **not yet established**. The per-rule attribution run was
started and lost. Note that `first_bound` (P0-4, since fixed) was a *plausible*
suspect — it accepted non-ground compound terms as index keys — but it would
cause *missed* derivations, not extra scans, so it is probably not the whole
story. Do not assume; re-instrument per rule.

### I2 — `saturate_naive` is broken — FIXED (stale join cursors)

The benchmark baseline in `src/solver_fwd.rs` derived ~1 200 facts where ~180 900
are correct, which invalidated the semi-naive-vs-naive comparison entirely.

### I3 — Two benchmarks measure nothing

`db_index_lookup` and `db_scan_lookup` in `benches/kernel.rs` call `.len()` on a
slice, which is O(1). They measure a pointer read, not a scan. Rewrite to touch
every returned tuple.

### I4 — `rss_kb()` is read after the solver drops

In `Bench::run`/`run_once` the closure owns and drops the `Solver` before the
harness reads RSS, so those figures **understate** peak memory. Read RSS inside
the closure. (The scaling table reads it while the solver is alive, so those
figures are valid — which is why the same suite reports both 3.1 GB and 6 MB.)

### I5 — The engine omits derivations the reference derives — FIXED

Was detected by `tests/soundness.rs::agrees_with_naive_reference_on_random_programs`
(`#[ignore]`d). On the generated family the engine missed facts such as
`q(4,4)` from `q(X,Y) :- p(X), e(_,Y).` when both `p(4)` and `e(4,4)` are present.
This is **incompleteness of saturation**, and it is the most serious open item:
it is the same class of bug as the four P0 defects already fixed, and it is
caught only because `tests/reference.rs` is a genuinely independent
implementation.

**Root cause (same for I6).** `eval_rule_inner` undid the substitution to the
rule-entry mark after every derived solution (`src/solver_fwd.rs`). That
discarded the seed bindings, and the join's resume logic (`undo_to(jm[0])` in
`next_solution`) became a no-op against the already-truncated trail — so the
first solution per seed was correct and every later one ran with unbound
variables. **Fix:** undo to the join's resume point (`jm[0]`, taken after the
seed matched) instead of the entry mark. Both `#[ignore]`s removed; the tests
stay as regression coverage.

### I6 — `non_ground_heads` is 3 on the transitive-closure fixture — FIXED

Was detected by `tests/soundness.rs::no_bindings_survive_saturation`
(`#[ignore]`d). A head really was coming out unresolved: the second and later
solutions per seed above. Same fix as I5; the canary reads 0 now.

### I7 — `proof.root` and `proof.steps` are never validated — FIXED

`check::verify` used to inspect only `proof.goal`, so a proof whose root
pointed at an unrelated derivation, or whose SLD trace was wrong, was
accepted, and `CheckErr::GoalMismatch` was dead code. Now: a present `root`
must conclude exactly the goal (`GoalMismatch` otherwise), and a resolution
trace replays step by step — each step's instantiation must reproduce its
conclusion and goal from the rule, and every positive premise must already
hold in the database or an earlier step (children-first order), with indexed
lookup where possible. Locked by `deep_backward_proof_with_fresh_variables_per_step`
(backward proofs verify) and `a_tampered_backward_proof_is_rejected`.

### I8 — The parser is recursive and the depth cap is a magic number — FIXED

`Parser::term` recursed. Now `Parser::atom` parses over an explicit frame
stack: depth costs heap frames, not native stack, so a 3000-deep term parses
on any thread size (the depth test keeps its 32 MiB thread and passes with
headroom to spare). Limits, positions and every error message are unchanged —
the rewrite parses left-to-right exactly like the recursion it replaced. The
4096 clamp stays, still owned by `TermStore::rename`'s truncation, not by the
stack.
