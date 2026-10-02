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

### A1. `prove` can return an unsound `Refuted`

**Severity: high. This is a wrong answer, not a missing feature.**

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

**What removes it.** Track, per goal, whether every rule that could derive it was
examined by *some* engine. Concretely: `prove` should return `Refuted` only when
`!prog.forward_rules_skipped_for(pred_of(goal))` and SLD did not bail on the
depth bound or on a skipped rule; otherwise `Status::Unknown`. `Status::Unknown`
already exists for exactly this (`src/status.rs:39`) and is never constructed
today — see A5. As a stopgap that costs nothing: if
`prog.rules_by_pred[pred].iter().any(|r| prog.rules[r].backward_only)`, refuse to
return `Refuted`.

### A2. `query` never uses the backward engine

`Solver::query` (`src/solver_bwd.rs:242-291`) saturates, then matches the goal
against `db.by_pred[pred]`. There is no SLD call anywhere in it. For a predicate
defined only by `backward_only` rules, `by_pred[pred]` is empty, so the answer is
`Status::Refuted` with an empty answer set and a saturation certificate. Same
defect as A1, with no depth or negation subtlety: `?- num(X).` over
`base(a). num(succ(X)) :- base(X).` returns "no answers" rather than "no
answers, or answers I did not look for".

**What removes it.** For a goal whose predicate has `backward_only` rules, drive
SLD over the finite candidate bindings of the non-`backward_only` arguments and
collect solutions; return `Unknown` rather than `Refuted` if the goal is not
ground.

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

**What removes it.** A branch in `Solver::verify` that dispatches on
`proof.saturation`: when it is `Some`, recompute and compare instead of calling
`atom_ok`. About fifteen lines.

### A4. `first_bound` can index on the wrong argument

`Solver::first_bound` (`src/solver_fwd.rs:121-131`) returns the value of the
**first bound argument**, at whatever position it occurs:

```rust
for i in 0..n {
    let a = self.prog.store.child(atom, i);
    let r = self.subst.find(a);
    if self.prog.store.kind(r) != T_VAR {
        return Some(self.subst.resolve(&self.prog.store, r));
    }
}
```

`Db::candidates` interprets that value as a **first-argument** key
(`src/db.rs:109-127`), because `by_first` is keyed on `store.args(atom)[0]`
(`src/db.rs:76-83`, `97-100`). When a literal's first argument is unbound but a
later one is bound, the two disagree, and the join searches an unrelated bucket
instead of the relation — silently losing derivations.

Reachable shape: a body literal whose first argument is an anonymous variable
while a later argument is bound by an earlier join level. `r(X,Y) :- s(Y,X),
p(_, X).` seeded at `s(Y,X)` does it. The generated corpus in
`tests/soundness.rs::generate_datalog` (`q(X,Y) :- p(X), e(_,Y).`) does not hit
it, which is why nothing has caught it.

Note the direction of the error: an empty bucket yields zero candidates, so this
*under*-counts work. It cannot explain the excess scans in C1.

**What removes it.** Either index lookup is guarded by
`store.child(atom, 0)` being bound, or `Db` grows a per-position index. The
one-line fix is to make `first_bound` only ever look at argument 0; the general
fix is the same second index level discussed in DD-0006.

### A5. `Status::Unknown` and `Status::Impossible` are never constructed

Both variants exist and are documented (`src/status.rs:32-40`), and
`is_inconclusive` / `requires_proof` are tested against them
(`src/check.rs:337-343`). Grepping every construction site in `src/` and
`tests/`: the only statuses any solver path produces are `Proved`, `Refuted`,
``Found`, and `Exhausted`.

This contradicts three written claims:

* `src/lib.rs:41-44` — "outside it, it returns `Unknown` or `Exhausted` rather
  than guessing". It never returns `Unknown`.
* `docs/ARCHITECTURE.md:159-162` — same claim.
* `src/solver_bwd.rs:22-24` — "`prove` therefore returns `Unknown` rather than
  pretending, when only backward search could apply and the ground restriction
  bites". It returns `Refuted`; see A1.

Either the claims are wrong or the engine is. **A1 is the fix that makes the
claims true.** Until then, treat the prose as aspirational.

Related: `Exhausted::Depth` (`src/status.rs:88`) is also never constructed. The
SLD depth bound returns `Ok(false)` (`src/solver_bwd.rs:57-59`), which is what
feeds the unsound `Refuted` in A1(iii) — the engine has a status for exactly
this situation and does not use it.

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

---

## B. Scope: logic that is not implemented

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

### B3. A negated body literal that is not fully instantiated blocks the derivation

**What it is.** `Solver::negatives_hold` (`src/solver_fwd.rs:98-116`) returns
`false` — blocking the derivation — when a negated literal resolves to a term that
still contains a variable, or when it matches a stored fact:

```rust
let a = self.subst.resolve(&mut self.prog.store, lit.atom);
if !self.prog.store.is_ground(a) {
    return false;
}
if self.db.contains(a) {
    return false;
}
```

**Why.** Soundness, not optimisation. Treating a partially instantiated
`not q(X)` as satisfied would derive facts that classical negation does not
license. Soundness over completeness, deliberately.

**Cost.** **The engine is incomplete for stratified Datalog**, which is
otherwise its home territory. Any program in which a negation is evaluated
before every variable in it is bound silently drops those derivations, and the
answer is presented as a definite `Refuted` rather than as `Unknown`. This is the
sharpest edge in the whole design and the one most likely to surprise a user.

Worked example of the incompleteness, by inspection:

```text
node(a). node(b). blocked(b).
safe(X) :- node(X), not blocked(X).
pair(X, Y) :- safe(X), safe(Y).
?- pair(a, a).
```

`pair(a,a)` follows: `safe(a)` holds because `blocked(a)` is absent. But during
the join for `pair`, `safe(X)` is seeded from the delta while `X` is still
partially determined, `negatives_hold` sees `not blocked(X)` as not ground, and
the derivation is blocked.

**What would remove it.** An anti-join / tabling evaluation for stratified
negation: instead of testing each candidate individually, compute the negation by
subtracting the negation predicate's closure from the cross-product of the
positive literals' closures. That is a new rule-evaluation strategy, not a patch.

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

### B7. No SAT, SMT, constraints, arithmetic, search, strategy selection, or neural components

Absent, in full, and named here so their absence is unambiguous
(`docs/ALGORITHMS.md` §8):

| Capability | Present? | Note |
|---|---|---|
| CDCL / SAT / clause learning / watched literals / VSIDS | no | planned first in `docs/ROADMAP.md` |
| Theory combination, CDCL(T), linear arithmetic, congruence closure | no | depends on the SAT core |
| Constraint propagators, domains, MAC search | no | and must record explanations — a propagator that removes a value without recording why cannot support a proof |
| Symbolic arithmetic: polynomials, intervals, identities | no | |
| Search: IDA*, A*, alpha-beta, transposition tables | no | |
| Strategy selection / solver portfolio | no | pointless with one engine |
| Partial evaluation / the charter's compiler passes | no | only constant folding and dead-static-rule elimination exist |

There are **no neural components**. DD-0013 records the decision and the
reasoning; nothing in the crate is a model, and nothing in `[dependencies]`
(DD-0007 keeps the dependency list empty).

**Cost.** The engine reasons over Horn programs and nothing else. Every family
above the line in `docs/ARCHITECTURE.md` §7 requires an adapter *and* a new
solver, not an adapter alone.

**What would remove it.** Each row, in the dependency order given in
`docs/ROADMAP.md` Stage 2.

### B8. No IR serialisation

**What it is.** There is no binary or textual IR dump. The only interchange
formats are the exterior's surface syntax and the Rust `Builder` API
(`docs/IR_SPEC.md` §10).

**Why it is hard.** The IR is a hash-consed arena. Node ids are positions in a
`Vec<TermNode>` plus offsets into a flat child vector, so a dump has to encode
the arena topology and the symbol table consistently, and reloading has to
reproduce identical ids or every recorded proof becomes invalid — `inst` is
keyed by rule-local variable ids and `concl` by arena node
(`docs/IR_SPEC.md` §8).

**Cost.** No persistent problems, no cross-process proofs, no shipping a model.
`show` (`src/exterior.rs:438`) renders rules back to text and is not
serialisation: it loses queries, loses original variable names, and loses the
symbol-id layout that proofs depend on.

**What would remove it.** A versioned arena format plus a rehash-on-load pass, and
a decision — recorded, not assumed — about whether proofs survive a round trip
through it.

---

## C. Performance and memory

### C1. Transitive closure examines `≈ 0.5·n³` candidates where `0.5·n²` is correct

**The measurement.** On a path graph with `n` nodes, `candidates` grows as
approximately **`0.5 · n³`**. The correct figure is **`0.5 · n²`** — the number
of `path` tuples the closure contains. (`idb_facts` additionally counts the `n`
`edge` facts, because a fact-only predicate is IDB; DD-0017. The expected total
is `n(n+1)/2 + n`.) At **n = 800**, instrumentation counted approximately
**292 million UNBOUND (non-indexed) scans**, while bound index lookups were a
healthy **427 thousand**. Reproduce with:

```sh
cargo bench --bench kernel -- diag
```

which prints `n`, `facts`, `rounds`, `derivations`, `candidates` and wall time
for n ∈ {100, 200, 400, 800} (`benches/kernel.rs:513-532`).

**Note on provenance.** These figures are instrumented, not written down: no
checked-in document contains them, and `docs/PERFORMANCE.md` — referenced from
`src/solver.rs:42`, `src/term.rs:247`, `src/subst.rs:68`, `src/budget.rs:11` and
`docs/ALGORITHMS.md:157` — does not exist. They must be re-derived and recorded
before they are trusted.

**The root cause is not established.** That is the honest statement. What can be
ruled out from the code:

* `Solver::first_bound` (`src/solver_fwd.rs:121-131`) does inspect *all* arguments
  of the literal, not only the first, so "we only look at argument 0" is not the
  explanation.
* `Db::candidates` with `bound_first = Some(k)` returns an empty slice for an
  unknown predicate or an absent key (`src/db.rs:109-127`), so a wrong key
  *reduces* scans. A4 is a real bug but cannot be the cause of excess scans.
* `by_first` is populated for every insert (`src/db.rs:97-100`) and
  `first_bound` resolves through the substitution, so the key is a hash-consed
  node id and cannot silently miss.

What remains is a path where `first_bound` returns `None` when it should return
`Some`. The discriminator is one counter: increment a `unbound_scans` and a
`bound_scans` counter in `next_solution` around the `db.candidates` call
(`src/solver_fwd.rs:193`) and attribute them by `(rule id, body position)`. One
diag run then names the rule shape responsible, instead of leaving it to
inference.

**Cost.** Transitive closure is O(n³) instead of O(n²) in examined tuples. That
is a factor of *n*, so it is not a constant-factor problem and will not be
absorbed by faster hardware.

**What would remove it.** Finding the cause. The second index level (DD-0006)
would not help if the problem is that the index is not being used; a
selectivity-ordered or magic-set rule rewriting would help if it is that the
wrong body position is seeded. Do not guess: instrument first.

### C2. ~248 bytes per derived fact, of which ~19 is IR payload

**The measurement.** A closure of 12.5 M facts cost 3.1 GB RSS — about **248 B
per fact** against roughly **19 B of IR payload** (DD-0014; the harness comment
at `benches/kernel.rs:422` records the same figure). The attribution benchmark
prints `rss`, `store`, `db_indexes`, `deriv_records` and the per-fact ratios for
`ProofMode::Full` and `ProofMode::Off` (`benches/kernel.rs:427-476`) — but note
A7: its RSS column is read after the solver is dropped, so only the `store` and
`db_indexes` columns are trustworthy as written.

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

### C5. One index level

`Db` ships a per-predicate vector plus a first-argument hash index
(`src/db.rs:37-48`). DD-0006 records the measurement behind that decision
(50 000 tuples over 500 distinct first arguments: 2.31 × 10⁹ tuples examined by
scan against 4.67 × 10⁶ by index, 495.8× fewer) and the trigger that would
reverse it. See `docs/ROADMAP.md`, "Triggers to revisit existing decisions".

---

## D. Summary table

| # | Item | Class | Wrong answers possible? | Fix cost |
|---|---|---|---|---|
| A1 | `prove` returns unsound `Refuted` | correctness | **yes** | small (stopgap) / medium (real fix) |
| A2 | `query` ignores the backward engine | correctness | **yes** | medium |
| A3 | `verify` ignores the saturation certificate | correctness | no, but weakens a stated guarantee | very small |
| A4 | `first_bound` can index on the wrong argument | correctness | **yes** (lost derivations) | very small |
| A5 | `Unknown` / `Impossible` never constructed | correctness | contradicts three written claims | small |
| A6 | `saturate_naive` derives 1 200 of 180 900 facts | correctness | **yes**, for benchmark figures only | small |
| A7 | two benchmarks measure nothing; RSS understated | measurement | no | small |
| A8 | raised `Limits` corrupt terms silently | correctness | yes, if limits are raised | small |
| B1 | stratified Datalog only | scope | no | large |
| B2 | undecidability | scope | no — not fixable | n/a |
| B3 | non-ground negation blocks derivations | incompleteness | reported as `Refuted` | large |
| B4 | `backward_only` heads | scope | contributes to A1/A2 | large |
| B5 | backward fragment restrictions | scope | contributes to A1 | medium |
| B6 | no negation in backward mode | scope | contributes to A1 | large |
| B7 | no SAT/SMT/CP/search/portfolio/neural | scope | no | large |
| B8 | no IR serialisation | scope | no | medium |
| C1 | `candidates ≈ 0.5·n³` vs `0.5·n²` | performance | no | unknown — cause unestablished |
| C2 | 248 B/fact vs 19 B payload | memory | no | medium, or use `ProofMode::Off` |
| C3 | least selective seed dominates | performance | no | large |
| C4 | no `resolve` memoisation | performance | no | small, needs a measurement |
| C5 | one index level | performance | no | small, trigger recorded |