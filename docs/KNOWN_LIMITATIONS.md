# KNOWN LIMITATIONS

An itemised, honest account of what this engine does not do, why, what it costs,
and what would change it.

This document is the project's credibility anchor. If a claim here and a claim in
`README.md` disagree, this document is the one to believe. Every non-obvious
statement below cites the file and line that establishes it, or is labelled as a
measurement whose reproduction command is given. Nothing is claimed that is not
implemented.

**Reading order.** Section A is a list of *correctness risks* — places where the
engine can produce or appear to produce a wrong answer, or where a stated
guarantee is weaker than the prose implies. Section B is *scope*: logic that is
not implemented. Section C is *performance and memory*.

---

## A. Correctness risks

### A1. `prove` can return an unsound `Refuted` — FIXED via decline/`Unknown`

**Severity when open: high. This was a wrong answer, not a missing feature.**

`Solver::prove` decides a goal in this order (`src/solver_bwd.rs:156-235`):

1. saturate bottom-up; if saturation ran out of budget, remember it;
2. if the goal is in the database, return `Proved`;
3. otherwise run depth-bounded SLD;
4. if SLD returns "no" **and** saturation completed, return **`Refuted`** with a
   closure certificate (`src/solver_bwd.rs:207-232`).

Step 4 is where the guarantee breaks. Saturation **silently skips every
`backward_only` rule** (`src/solver_fwd.rs:391-393`), so a completed saturation
certifies the least model *of the forward-chaining fragment only*. SLD, in turn,
silently skips any candidate rule that contains a negated body literal
(`src/solver_bwd.rs:93-100`) or a subgoal that is not ground after resolution
(`src/solver_bwd.rs:101-106`). When a rule is skipped by *both* engines, SLD
returns "no" not because the goal is unprovable but because the goal was never
examined — and step 4 reports that as `Refuted`.

Programs that trigger it, by inspection of the code paths above (these have not
been executed: there is no Rust toolchain on the machine this document was
written on):

```text
# (i) negation inside a backward_only rule body
base(a).
p(f(X)) :- base(X), not q(X).
?- p(f(a)).
```

```text
# (ii) a non-ground subgoal inside a backward_only rule body
base(a).
holds(a, b).
p(f(X)) :- base(X), holds(X, _).
?- p(f(a)).
```

```text
# (iii) a backward_only chain longer than the depth bound (64, src/solver_bwd.rs:42)
link(z, w).
link(X, f(Y)) :- link(X, Y).
?- link(z, f(f(...f(w)...))).     -- 70 nested f/1
```

In all three, `p(f(a))` / `link(z, f^70(w))` is in the model, the rule is
`backward_only`, saturation completes without deriving it, SLD declines it, and
step 4 returns `Refuted` with the note *"bottom-up saturation completed; goal
absent from the least model"*.

**The certificate does not catch this.** `check::verify_saturation`
(`src/check.rs:208-216`) compares the recorded fingerprint against
`recompute_saturation(prog)`, which re-runs the *same* skip-everything-`
backward_only` saturation. Both hashes agree, so the refutation verifies. The
certificate attests to determinism, not to completeness.

**What removed it.** The backward engine is tri-state (`SldOutcome::Proved /
NotProvable / Declined`, `src/solver_bwd.rs`): "no rule derives this goal" and
"I did not look" (depth bound, negated body literal, non-ground subgoal) are
different return values, and only `NotProvable` licenses `Refuted` — a decline
yields `Status::Unknown`. Locked by three regression tests in
`tests/soundness.rs` (`refutation_is_never_unearned_*`) built from the programs
(i)–(iii) below, each asserting `Unknown`, not `Refuted`.

### A2. `query` never uses the backward engine

`Solver::query` (`src/solver_bwd.rs:242-291`) saturates, then matches the goal
against `db.by_pred[pred]`. There is no SLD call anywhere in it. For a predicate
defined only by `backward_only` rules, `by_pred[pred]` is empty, so the answer is
`Status::Refuted` with an empty answer set and a saturation certificate. Same
defect as A1, with no depth or negation subtlety: `?- num(X).` over
`base(a). num(succ(X)) :- base(X).` returns "no answers" rather than "no
answers, or answers I did not look for".

**What removed the unsound half.** An empty answer set is `Refuted` only when
no `backward_only` rule exists for the goal's predicate; otherwise the answer
is `Unknown` with the completed forward closure still attached
(`src/solver_bwd.rs`, `tests/soundness.rs::query_with_backward_rules_and_no_answers_is_unknown`).
Driving SLD over candidate bindings to *collect* backward answers (rather than
merely refusing `Refuted`) is still future work.

### A3. `Solver::verify` ignores the saturation certificate

`Solver::verify` calls `check::verify`, whose entire body is `c.atom_ok(proof.goal)`
(`src/check.rs:194`). For a `Refuted` proof the goal is absent from the database
and has no derivation, so `verify` returns `Err(CheckErr::Unsupported { .. })` —
even though `proof.saturation` is present and checkable. The negative certificate
is *produced* by `prove` but is only verifiable by calling
`axiom::check::verify_saturation(&recorded, &axiom::solver::recompute_saturation(&prog))`
directly. There is no `Solver` method that does this.

The claim "every definite answer carries a machine-checkable proof" is therefore
true for `Proved` and false, as written, for `Refuted`. The proof object is
there; the check is not wired up.

**What removed it.** `Solver::verify` dispatches on `proof.saturation`: when
present it recomputes the closure from scratch and compares fingerprints
(`check::verify_saturation`). About fifteen lines, as predicted.

### A4. `first_bound` can index on the wrong argument — FIXED by construction

`Solver::first_bound` used to return the value of the **first bound argument**,
at whatever position it occurred, while `Db::candidates` read that value as a
**first-argument** key. Fixed twice: first by restricting the old function to
argument 0, then properly by making the key position-tagged —
`bound_key` returns `(pos, key)` for argument 0 else argument 1, and
`Db::candidates` consults the matching level. The confusion is now
unrepresentable, and both levels are covered by `db.rs` unit tests plus the
`db_index_lookup[_arg1]` benchmark rows.

The old shape, for the record: the function scanned *all* arguments
(`src/solver_fwd.rs`), so on a literal like `p(_, X)` with `X` bound the join
read an unrelated first-argument bucket and silently lost derivations (an
empty bucket yields zero candidates, so it *under*-counted work and cannot
explain the excess scans in C1). The differential corpus
(`q(X,Y) :- p(X), e(_,Y).`) never hit it, which is why nothing caught it.

### A5. `Status::Unknown` is now constructed; `Status::Impossible` is reserved

`Status::Unknown` is returned whenever backward resolution declines
(`SldOutcome::Declined`), for foreign-store goals (`Exhausted::Malformed`),
and for queries whose predicate has unexamined `backward_only` rules — so the
prose in `src/lib.rs:41-44`, `docs/ARCHITECTURE.md:159-162` and
`src/solver_bwd.rs:22-24` is true, not aspirational. `Exhausted::Depth` is
constructed for depth declines. `Status::Impossible` remains unconstructed by
design: it becomes reachable with constraint propagators (ROADMAP II3), where
a pruned-everything domain carries the same certificate discipline as
`Refuted`.

### A6. `saturate_naive` returns a wrong least model

`Solver::saturate_naive` (`src/solver_fwd.rs:436-465`) is the benchmark baseline
for `semi_naive_vs_fixpoint`. **It is known buggy and its output is not the least
model**: it derives roughly **1 200** facts where roughly **180 900** are correct
on the n = 600 path graph used by that benchmark. It has the right termination
condition (`new_facts` unchanged) but does not enumerate all solutions per firing,
so it stops at a fixpoint of its own incomplete search rather than of the program.

No solver path calls it — it is reachable only from `benches/kernel.rs:309`.
Until it is fixed or deleted, any figure derived from it is a figure about a bug,
and `ALGORITHMS.md` §7's comparison table cannot be filled in from it.

**What removes it.** Either port the resumable `next_solution` loop that
`saturate` uses (the naive loop's real difference is that it re-evaluates every
rule every round with no delta, which is a one-line change in `eval_rule`'s
caller) or delete the function and re-baseline the comparison against a
straightforward string-based fixpoint.

### A7. Two benchmarks measure nothing; the RSS column understates peak

* **`db_index_lookup` and `db_scan_lookup` (`benches/kernel.rs:277-291`) do not
  measure index lookups.** Both call `db.candidates(pred, …).len()`, which is
  `slice::len` — O(1). Both therefore measure the cost of 50 000 O(1) length
  reads, and their "Mops/s" and "allocs/it" columns say nothing about indexing.
  The printed selectivity figures just above them (`scan_total`, `index_total`,
  and the 495.8× ratio in DD-0006) are computed from the same `.len()` calls, so
  they are correct as *counts of tuples that would be examined* and must not be
  read as timings.
* **`rss_kb()` is read after the solver has been dropped.** `Bench::run` and
  `Bench::run_once` evaluate `rss_kb` while building the `Row`, after `f` has
  returned (`src/bench.rs:236` and `src/bench.rs:258`). Every closure in the
  suite that wants memory constructs and drops its `Solver` inside `f`, so the
  solver's peak is gone before the sample. The `rss kB` column therefore reports
  post-solve residency and **understates peak memory**. `peak_rss_kb()` (reading
  `VmHWM`) exists at `src/bench.rs:85` but is only passed to `black_box` in the
  scaling table (`benches/kernel.rs:575`); it is never recorded in a `Row`.
* **The summary table prints a blank row per measurement.** `Bench::push` takes
  its `Row` argument by value, ignores it (`let _ = row;`, `src/bench.rs:209`),
  and every caller follows the real `rows.push` with
  `self.push(Row::default_stub())` (`src/bench.rs:239`, `262`, `290`). `report`
  then prints all of them. Every `rss_kb` figure in the summary is therefore
  printed twice: once real, once as zeros.

**What removes it.** Make the benchmarks consume the tuples (touch the `TermId`s,
e.g. accumulate them through `black_box`) rather than calling `len()`; move the
RSS sample inside the timed region or switch the column to `peak_rss_kb()`; delete
the stub rows.

### A8. Raising `Limits` past two internal bounds corrupts silently

Both are unreachable under `Limits::default()`; both are reachable the moment a
caller raises a limit. Detail in `docs/LANGUAGE_SPEC.md` §4.1.

* `max_arity > 65_535`: `TermNode.len` is a `u16` (`src/term.rs:51`), stored as
  `args.len() as u16` (`src/term.rs:229`). Arity 65 536 stores `len = 0` and the
  atom silently loses every argument.
* `max_depth > 4096`: `TermStore::rename` returns subterms **un-renamed** past its
  hard-coded `const MAX: usize = 4096` (`src/term.rs:288-292`), so a deeply nested
  rule gets a renamed copy whose inner variables were never freshened.
   `tests/robustness.rs:218-225` already parses a 200 000-deep term under
   `max_depth: 500_000`; that program has no rules, so the bug is not reached
   today.

### A9. Backward resolution reused cached renamings across recursion — FIXED

**Severity when open: high. Wrong answers in both directions.**

`sld_ground` unified each candidate rule through the cached forward renaming
(`ensure_renamed`, built once per rule). Forward chaining reuses it soundly
because every firing is enclosed in a trail mark; backward search recurses
through the same rule with the parent's bindings still live, so the child's
unification saw the parent's values: a goal 10 deep over
`link(X, f(Y)) :- link(X, Y).` clashed at depth 1 and reported `Refuted` —
for a goal that is *provable*. Found by the new A1(iii) regression test
(`refutation_is_never_unearned_beyond_depth_bound`), which failed with
`Refuted` where `Unknown` was expected, and confirmed by an SLD trace showing
no call past depth 1.

**What removed it.** `Solver::freshen_rule` (`src/solver_bwd.rs`): every SLD
step maps the rule's locals to new fresh variables. Regression coverage both
ways: `deep_backward_proof_with_fresh_variables_per_step` (10 deep proves)
and the A1(iii) depth-bound test (70 deep is `Unknown`).

---

## B. Scope boundaries and root-engine gaps

### B1. Stratified Datalog only. Not a theorem prover.

**What it is.** Facts, rules with a single positive head, positive and
stratified-negated body literals, one fixed point. `src/program.rs:4-24`,
DD-0002.

**Why.** A decidable fragment with a *unique* least model is what makes `Refuted`
a real claim rather than "the search gave up". Half the value is in refusing
programs that have no least model instead of picking one.

**Cost.** No general first-order refutation. No clauses, no disjunction, no
quantifiers, no equality over non-ground terms, no Herbrand theorem. Proving
`p ∨ q` is out of reach; so is anything requiring more than one positive
alternative.

**What would remove it.** A saturation engine (ordered resolution with
paramodulation) as a *third* solver over the same IR — not an extension of
`Solver::saturate`. See `docs/ROADMAP.md` Stage 2.

### B2. Undecidability is not a resource problem

**What it is.** General first-order validity is undecidable. By Church's theorem
there is no sound *and* complete procedure for arbitrary quantified formulas.

**Why it is stated here.** Because it is the single most common misreading of
this project. It is not a matter of the engine being too slow, and no amount of
compute, memory, or a bigger machine changes it. A larger budget can turn
`Exhausted` into `Proved`; it can never turn `Exhausted` into a correct `Refuted`.
The only defensible response is to make partial knowledge representable in the
return type, which is why `Unknown` and `Exhausted` are first-class answers and
why there is no constructor for a solved status that carries no proof
(`src/status.rs:1-19`, `docs/ARCHITECTURE.md:134-139`).

**Cost.** Many individually-encodable families sit above NP. The engine will
never be a general answer to "solve this puzzle"; it can be a sound partial
answer.

**What would remove it.** Nothing. This is the reason `Status` exists in the
shape it does.

### B3. Negation scheduling — FIXED, with a remaining safety requirement

**What it was.** The forward engine tested `negatives_hold` immediately after a
delta seed, before later positive body literals had bound the negated
variables. A rule like

```text
p(X,Y) :- q(X), not r(Y), s(Y).
```

derived nothing, because `not r(Y)` was evaluated while `Y` was still unbound.
The check also ran once per seed rather than once per completed join.

**Fix.** The premature check was removed from `eval_rule_inner`; negation is
now tested only after the positive join completes. Regression:
`tests/soundness.rs::negation_waits_for_later_positive_bindings`, which requires
`p(a,b)` and `p(b,b)`.

**Remaining limitation (updated).** Forward rules now pass a safety check:
every head variable and every variable in a negated literal must be bound by a
positive body literal. Unsafe forward rules are rejected as `UnsafeRule` rather
than silently deriving an incomplete closure. `backward_only` function-head
rules are exempt from the head check and can still decline on non-ground
negation.

**What would remove the remaining limitation.** An anti-join/tabling strategy
that handles non-ground negation explicitly for `backward_only` rules. The v4
Datalog adapter now exposes the rejection instead of documenting silent
incompleteness.

### B4. Function symbols in rule heads are `backward_only`

**What it is.** `Builder::head_is_unenumerable` (`src/program.rs:366-383`) marks a
rule `backward_only` if any `T_FUN` node appears anywhere under its head. Such
rules are skipped by `saturate` and `saturate_naive`
(`src/solver_fwd.rs:391-393`) and are only reachable by backward resolution.

**Why.** The relation has an infinite domain (`num(succ(X))`, `link(X, f(Y))`).
Bottom-up saturation cannot enumerate an infinite relation, and the alternatives
— storing non-ground facts, or looping — are both worse.

**Cost.** Two costs, not one:

1. Saturation's closure is not the least model of the program, only of its
   forward-chaining fragment. Everything downstream inherits this — see A1 and A2,
   which are the real cost.
2. `Program::forward_rules()` reports how many rules were skipped, so the cost is
   visible but the *answers* are not qualified.

**What would remove it.** A tabling / memoised resolution engine with a
generalising answer representation, which is the standard answer and is a
substantial piece of work. Short of that, A1's stopgap (refuse `Refuted` when a
`backward_only` rule could apply) contains the damage.

### B5. Backward resolution: ground goals, positive bodies, depth 64

**What it is.** `sld_ground` (`src/solver_bwd.rs:48-138`) implements depth-bounded
SLD with failure memoisation keyed by `(goal, depth)`. It refuses:

* a negated body literal — `if !lit.pos { ok = false; break; }`
  (`src/solver_bwd.rs:97-100`);
* a subgoal that is not ground after resolution — `if !self.prog.store.is_ground(sub)
  { ok = false; break; }` (`src/solver_bwd.rs:101-106`);
* any goal deeper than `DEFAULT_MAX_DEPTH = 64` (`src/solver_bwd.rs:42`,
  `57-59`).

Note these are *rule-level* skips, not goal-level failures: one bad body
literal disqualifies the whole rule for that goal.

**Why.** Negation-as-failure would make `Proved` unfalsifiable; non-ground
backward search needs tabling to be *complete*, and an incomplete version under
the same status enum is worse than no version. That reasoning is correct and is
recorded in `src/solver_bwd.rs:14-24`.

**Cost.** The refusal mechanism is the bug in A1: "I declined" and "it is false"
are the same return value. The two must be distinguishable.

**What would remove it.** Distinct return values — `Declined` versus `Failed` —
plus a per-goal "was every candidate rule examined?" flag. That is A1's fix and
it converts three of these four refusals from unsound into honest `Unknown`.

### B6. A partially instantiated `not` is not supported in backward mode

Covered by B5's first two bullets but called out separately because the task of
eliminating it is different. B3 is about bottom-up evaluation of negation;
this is about resolution never having a negation case at all. There is no code
path in `src/solver_bwd.rs` that examines `Literal::pos == false`. Nothing
approximates it; nothing warns about it either, beyond the refusal in A1's shape.

**Cost.** Any program needing both an infinite-domain head *and* negation is
outside the engine entirely.

**What would remove it.** Tabled resolution with a well-founded negation
evaluation, plus proof recording for the negated goal. Substantially more than a
flag flip, and it is not on the Stage-2 roadmap for that reason.

### B7. Capability boundaries after v4

Some earlier absences are now implemented. The table records the current state;
details and evidence are in `docs/v4/CAPABILITY_MATRIX.md` and
`docs/v4/SEMANTICS.md`.

| Capability | Present? | Note |
|---|---|---|
| CDCL / SAT / learning / watched literals / VSIDS | **yes** | RUP-checked, frozen corpus |
| CDCL(T), integer difference logic, congruence closure | **yes** | checked models, replayed theory lemmas; no general arithmetic |
| Incremental theory solving / push-pop | no | single-shot driver |
| General linear/real arithmetic, arrays, bitvectors, strings | no | outside the fragment |
| Constraint propagation with explanations | **yes** | finite-domain CSP/puzzles |
| Search: A*, IDA*, alpha-beta, Dijkstra | **yes** | explicit graphs/trees, bounded |
| ASP: grounding, choice rules, stable models | **yes** | finite universe, 22-atom cap |
| FOL resolution with a trusted kernel | **yes** | bounded; no equality; never `Refuted` |
| Untyped STRIPS planning | **yes** | A* `h_max` / BFS; no costs/typed PDDL |
| Strategy selection / portfolio | partial | V2 chooser; router dispatches by kind |
| SMT-LIB / TPTP | no | not implemented |
| External differential comparison | partial | small manual harness; no conformance claim |
| Neural components | no | nothing in the crate is a model |

**Cost.** The platform is a set of scoped fragments, not a general prover. Every
row marked no requires a new solver or adapter, not just a document change.

### B8. Root IR serialisation is still absent

**What it is.** The root hash-consed arena has no binary or textual IR dump. The
only interchange formats are the exterior's surface syntax and the Rust
`Builder` API (`docs/IR_SPEC.md` §10).

v4's `crates/axiom-ir` provides a typed structural IR and deterministic
S-expression serialisation, but it is **not** a serialisation of the root
arena and does not preserve root proof ids. It is used by the FOL and planning
crates for their own syntax.

**Why it is hard.** Root node ids are positions in a `Vec<TermNode>` plus offsets
into a flat child vector, so a dump has to encode arena topology and the symbol
table consistently, and reloading must reproduce identical ids or recorded
proofs become invalid.

**Cost.** No persistent root problems, no cross-process root proofs, no shipping
a root model.

**What would remove it.** A versioned root-arena format plus a rehash-on-load
pass, with an explicit decision about whether proofs survive the round trip.
`axiom-ir` serialisation is not a substitute.

---

## C. Performance and memory

### C1. Transitive closure examined `≈ 0.5·n³` candidates — FIXED, now `0.5·n²`

**The measurement.** Post-fix `diag`: candidates 9,900 / 39,800 / 159,600 /
639,200 for n ∈ {100, 200, 400, 800} (slope 2.00), zero unbound scans, exact
closures in 2 rounds, 0.41 s at n=800 (was 38.7 s). The pre-fix figures below
are kept as the record of what was wrong. (`idb_facts` additionally counts the
`n` `edge` facts, because a fact-only predicate is IDB; DD-0017. The expected
total is `n(n+1)/2 + n`.) Pre-fix at **n = 800**: approximately **292 million
UNBOUND (non-indexed) scans** against **427 thousand** bound lookups.
Reproduce either era with:

```sh
cargo bench --bench kernel -- diag
```

which prints `n`, `facts`, `rounds`, `derivations`, `candidates` and wall time
for n ∈ {100, 200, 400, 800} (`benches/kernel.rs:513-532`).

**Note on provenance.** These figures are now recorded in
`docs/v4/BASELINE.md` from a named CI run. The old `docs/PERFORMANCE.md`
references were stale; there is no such file. Re-derive with the `diag` job
before trusting a changed number.

**The root cause is established by attribution.** What can be ruled out from
the code:

* `Solver::bound_key` inspects arguments 0 and 1 for a ground value, so "the
  index key is available but unused" is not the explanation — at the hot
  literal no indexed position is bound at all.
* `Db::candidates` with a bound key returns an empty slice for an unknown
  predicate or an absent key, so a wrong key *reduces* scans. A4 is fixed and
  cannot be the cause of excess scans.
* Both levels are populated for every insert and `bound_key` resolves through
  the substitution, so a key is a hash-consed node id and cannot silently miss.

What remains was a path where the index is not consulted at all, and the
`scan_attr` attribution (`Solver::scan_attribution`, printed by `diag`) named
it: the recursive rule `path(X,Z) :- path(X,Y), edge(Y,Z)` fired at the edge
position leaves `path(X,Y)` with nothing bound, so every edge-seeded firing
scans all of `path`. At n=800: 51B tuples offered unbound at (rule, pos 0)
against 639k bound at pos 1. The `bound_key` correctly returns `None` there —
no usable bound argument exists at the indexed positions — so the fix is a
second index level for the position that *is* bound (argument 1, `Y`), not a
smarter `bound_key`.

**Cost.** Transitive closure is O(n³) instead of O(n²) in examined tuples. That
is a factor of *n*, so it is not a constant-factor problem and will not be
absorbed by faster hardware.

**What removes it.** The second index level (argument 1): an edge-seeded
firing looks up `path(X, Y-bound)` in `by_second` instead of scanning. With
in-degree-bounded buckets on the path graph the total becomes O(n²).
Selectivity-ordered seeding or magic sets would address the same shape more
generally and remain future work; dropping the edge-seeded firing outright
would be unsound (new edge facts must propagate).

### C2. ~324 bytes per derived fact, of which ~20 is IR payload

**The measurement.** Post-second-index CI bench (`memory`, n=1000 path graph,
501,500 facts): **324 B/fact** RSS with proofs on (store 20 + db+deriv 89 +
allocator overhead/residency), **197 B/fact** with `ProofMode::Off`. Pre-index
the figures were 248 / ~19 (DD-0014): the second level cost ~76 B/fact for a
95× speedup. The attribution benchmark prints `rss`, `store`, `db_indexes`,
`deriv_records` and the per-fact ratios for both modes; its RSS column now
reads the process high-water mark (I3), so it no longer understates.

**Why.** Every derived fact records a `Derivation` holding two `Vec`s, each a
separate heap block (`src/proof.rs:17-29`). Proof logging is not a tax on the
algorithm; it *is* the memory cost.

**Cost.** Roughly an order of magnitude over the facts themselves. On a 7 GB box
this is the difference between solving a problem and not solving it.

**Mitigation.** `ProofMode::Off` (`src/solver.rs:50-56`) exists for exactly this.
The status contract is preserved: with `Off` the engine reports `Found`, not
`Proved`, because it has nothing to check (`src/solver_bwd.rs:180-184`). `Off`
must be set before solving (`src/solver.rs:153-157`).

**What would remove it.** Interning the two `Vec`s into one allocation, or
storing derivations in a flat arena with offsets — the same fix that IR
serialisation needs (B8). Until then `ProofMode::Off` is the answer and callers
must know to reach for it.

### C3. Mixed semi-naive is dominated by its least selective seed

Seeding each body position in turn (mixed, `src/solver_fwd.rs:12-16`) costs
`|body|` firings per rule per round, and the total is dominated by the *least*
selective position. The benchmark suite documents a concrete instance —
seeding at the `edge` position of the transitive-closure rule leaves `path(X,Y)`
with nothing bound and forces a full scan of a relation with millions of tuples
(`benches/kernel.rs:333-339`). `tc_random_n1500` is sized deliberately small
because of it.

**Cost.** The random-graph workload is roughly two orders of magnitude more
expensive per derived fact than the path graph. It is recorded rather than tuned
away, because "the measurement is the point".

**What would remove it.** A selectivity estimate per body position, or magic
sets. Both are real work and neither is correct before C1 is understood, since
C1 may be the same defect seen from the other side.

### C4. No memoisation in `resolve`

`Subst::resolve` (`src/subst.rs:328-363`) is iterative post-order with reusable
scratch vectors and no cache. A `ResolveCache` type was written and deleted
(DD-0012). Reintroduction requires a measurement that does not exist yet.

### C5. Two index levels (positions 0 and 1)

`Db` ships a per-predicate vector plus first- and second-argument hash indexes
(`src/db.rs`). DD-0006 records the measurement behind the first level
(50 000 tuples over 500 distinct first arguments: 2.31 × 10⁹ tuples examined by
scan against 4.67 × 10⁶ by index, 495.8× fewer) and the I1 attribution behind
the second (edge-seeded steps scanning `path` unbound). Positions 2+ stay
unindexed; the trigger for a third level is in `docs/ROADMAP.md` with DD-0006.

---

## D. Summary table

| # | Item | Class | Wrong answers possible? | Fix cost |
|---|---|---|---|---|
| A1 | unsound `Refuted` (FIXED via decline/`Unknown`) | correctness | **was yes** | done |
| A2 | `query` ignores the backward engine (FIXED stopgap: `Unknown`) | correctness | **was yes** | done (collection future) |
| A3 | `verify` ignores the saturation certificate (FIXED) | correctness | weakened a guarantee | done |
| A4 | wrong-argument index key (FIXED by position-tagged keys) | correctness | **was yes** | done |
| A5 | `Unknown` never constructed (now constructed; `Impossible` reserved) | correctness | claims now true | done |
| A6 | `saturate_naive` wrong model (FIXED: stale cursors) | correctness | **was yes**, benchmarks only | done |
| A7 | benchmark/RSS defects (open) | measurement | no; numbers misleading | small |
| A8 | raised `Limits` corrupt terms silently | correctness | yes, if limits are raised | small |
| A9 | SLD reused cached renamings across recursion (FIXED) | correctness | **yes**, both directions | small |
| B1 | stratified Datalog only | scope | no | large |
| B2 | undecidability | scope | no — not fixable | n/a |
| B3 | negation scheduling (FIXED); non-ground negation blocks | incompleteness | unsafe programs only | small safety check or large tabling |
| B4 | `backward_only` heads | scope | contributes to A1/A2 | large |
| B5 | backward fragment restrictions | scope | contributes to A1 | medium |
| B6 | no negation in backward mode | scope | contributes to A1 | large |
| B7 | scoped fragments: no general arithmetic, incremental theory, ASP aggregates, FOL equality, or external parity | scope | no | large |
| B8 | root IR serialisation absent (`axiom-ir` is separate) | scope | no | medium |
| C1 | join scaled n³ (FIXED: second index, slope 2.00, 0 unbound) | performance | no | done |
| C2 | 324 B/fact vs 20 B payload (was 248; +76 for the 95× speedup) | memory | no | medium, or use `ProofMode::Off` (197) |
| C3 | least selective seed dominates | performance | no | large |
| C4 | no `resolve` memoisation | performance | no | small, needs a measurement |
| C5 | two index levels (positions 0 and 1) | performance | no | done; trigger for 3rd recorded |