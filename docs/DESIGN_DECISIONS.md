# DESIGN DECISIONS

Each entry: **hypothesis → alternatives → what was measured → decision.**
Decisions that were reversed are kept, with the reason. A rejected experiment
that produced a clear conclusion is a result, not a failure.

Numbering is stable; do not renumber.

---

## DD-0001 — One IR, several solvers, each lowering it

**Hypothesis.** A single term-based IR can serve deduction, constraints, search,
and mathematics without per-domain code in the core.

**Alternatives.** (a) One evaluator over one representation. (b) Separate engines
with private representations and adapters between them. (c) A tagged union
supporting every theory natively.

**Decision.** (b) — one IR as the interchange format, several engines each
lowering it into a form they execute quickly.

**Reasoning.** (a) is the tempting reading of "general through representation"
and it is wrong: a hash-consed DAG is poor for interval arithmetic and for flat
literal arrays. (c) is a monolith wearing a union type; every engine then pays
for every theory. (b) keeps the core ignorant of domains — which is the actual
architectural requirement — while letting each engine be fast. The charter's own
§9 ("compile into a lower-level representation optimized for execution")
anticipates the lowering step.

**Consequence.** The IR is not the hot data structure. That is the point, and it
is the thing most likely to be forgotten by a future contributor.

---

## DD-0002 — Stratified Datalog, not Prolog

**Hypothesis.** A decidable fragment with a unique least model is the right
Stage-1 target, because it makes soundness claims possible rather than merely
asserted.

**Decision.** Facts and rules; single positive head; stratified negation;
bottom-up saturation as the primary engine; SLD as the secondary.

**Reasoning.** Negation-as-failure is a database idiom, not a logical one: under
it "is this true" has no answer and completeness claims are meaningless.
Stratification gives a well-defined least fixed point that the engine computes
*exactly*, so `Refuted` becomes a real claim. Half of the value here is that a
class of inputs has no least model and the builder refuses them rather than
picking one.

**Cost.** General first-order refutation is out of scope. Accepted.

---

## DD-0003 — The occurs check is mandatory and linear

**Hypothesis.** Occurs checking is soundness-critical, not an optimisation, and
can be made cheap.

**Decision.** Always on, generation-stamped so it is linear in the offending
term and allocation-free after warm-up.

**Reasoning.** Union-find merging `x` with `f(x)` builds a cyclic term graph;
afterwards every traversal is an infinite loop and `resolve` never returns. It is
a correctness requirement.

**Revealed bug.** `occurs` initially shared its work stack with `unify` and
`match_into`. Being called *from inside* the unification loop, its `clear()`
discarded sibling argument pairs still queued for matching, so only the **first**
variable of any compound literal ever bound. Everything looked plausible; the
symptom was an incomplete least model. Separate stacks fixed it. This is the
clearest example in the project of a memory-reuse optimisation silently destroying
correctness.

---

## DD-0004 — Link direction is fixed, not chosen by union-by-rank

**Hypothesis.** Union-by-rank is the right merge strategy.

**Decision.** Rank only for variable↔variable merges. A variable is *always*
attached underneath a non-variable.

**Reasoning.** `resolve` means "follow to the representative", so the
representative must be the more concrete side. Plain union-by-rank elects a
variable as root when it has accumulated rank and meets a function term, and the
binding then becomes invisible — a silent wrong answer. Chains follow term
nesting and are bounded by term depth, which `resolve` already walks.

---

## DD-0005 — No path compression in the substitution

**Hypothesis.** Compression speeds up `find` enough to be worth it.

**Decision.** Off. Union by rank bounds variable-only chains at O(log n).

**Reasoning.** Compression rewrites must be trailed so they can be undone on
backtracking, inflating both the trail and the undo cost. With compression off,
chains follow term nesting, which the resolution walk visits anyway. The
comparison is runnable: the type parameter exists to keep the experiment honest.

**Status.** Stated expectation, not yet measured end-to-end. Recorded as
unfinished rather than dressed up as a result.

---

## DD-0006 — Index depth: one level, with the trigger recorded

**Hypothesis.** For hash-consed ground atoms, join cost is dominated by tuples
*examined*, and a first-argument index removes most of that at one extra `u32`
per fact. A second level pays off only on workloads with selective
non-leading arguments.

**Measured.** 50 000 tuples over 500 distinct first arguments: a full scan
examines 2.31 × 10⁹ tuples, the index 4.67 × 10⁶ — **495.8× fewer**, or 92.4
tuples examined per lookup instead of 50 000.

**Decision.** One level. The Stage-1 suite has no representative workload with
selective second arguments, so adding one now would be speculative.

**Trigger to revisit.** A benchmark family where the leading argument has low
selectivity and a later argument is highly selective. Recorded in `ROADMAP.md`.

---

## DD-0007 — Zero runtime dependencies; external solvers as oracles only

**Hypothesis.** A large dependency stack is not needed, and pulling in an
existing prover would undercut the project's purpose.

**Decision.** Zero dependencies in `[dependencies]`. The benchmark harness is
hand-rolled (about 200 lines reading `/proc` and a counting global allocator)
because Criterion plus its tree would exceed the crate under test.

**Surveyed prior art.** `z3rs` (a pure-Rust Z3 port), `vampire-prover` bindings,
`foras`, `mrs`. All are real and none is used. Using Z3 would make the "core"
a black box and would mean the capability being demonstrated belongs to someone
else.

**Where external solvers belong.** As **test oracles** — which is exactly what
§11 asks for with "differential tests against trusted implementations". Nothing
external is ever in the shipped reasoning path. For Stage 1 the differential
test is `tests/reference.rs`, a deliberately naive string-based fixpoint sharing
no code with the engine; it is stronger evidence than Z3 would be here, because
it cannot share a bug.

---

## DD-0008 — Replace the default hasher for internal tables

**Hypothesis.** SipHash-1-3 is the wrong default for a structure-hashing engine.

**Decision.** `FxHasher` (rustc-hash construction) for all internal tables.

**Reasoning.** SipHash's unpredictability defends against hash-flooding by
*untrusted* keys. Here every key is produced by the engine itself, and the tables
compare keys, so unpredictability buys nothing while costing on the hottest path
in the system — term hash-consing.

**Honest note.** The speed difference has not been measured in isolation on this
codebase. The argument is sound; the number is not claimed. Both hashers produce
identical results, so an A/B cannot change any answer.

---

## DD-0009 — Rule renaming is done once and cached

**Hypothesis.** Renaming a rule's variables to fresh globals per derivation is
wasteful and can be hoisted.

**Decision.** Each rule is renamed exactly once, lazily, and the fresh copy is
reused for every firing.

**Soundness.** This is only safe because each firing is enclosed in a trail mark
and fully undone. A leaked binding would make reuse unsound.
`tests/soundness.rs::no_bindings_survive_saturation` and the resolution unit
tests hold the invariant. This is a good example of a performance change whose
justification is a soundness invariant that must be tested elsewhere.

---

## DD-0010 — The checker must not share the solver's code

**Hypothesis.** A proof checker that reuses the solver's substitution cannot
catch a bug in unification.

**Decision.** `check.rs` implements instantiation and matching as a structural
comparison against recorded atoms, over a plain `FxHashMap<u32, TermId>`, with
its own recursion and its own failure modes. It uses only `&TermStore`.

**Two revisions, both instructive.** The first draft built a parallel term store
so it could construct comparison terms — unsound, because node ids are only
meaningful *within* one store. The second draft compares structurally and
allocates nothing, which also removed the aliasing problem entirely.

**Why this is worth duplicating.** Unification is the highest-value soundness
component in the engine. Two independent implementations that must agree turn
that bug class into a test failure rather than a silent wrong proof.

---

## DD-0011 — `join` is a resumable generator

**Hypothesis.** A `join` that enumerates all solutions in one call and returns
the last is good enough, since the caller re-runs the rule.

**Decision.** Reversed. `next_solution` is resumable; the caller loops until
exhaustion.

**Why it was reversed.** The A/B benchmark showed semi-naive evaluation running
**350× slower** than the naive baseline, with 552 248 allocations against 4 441.
That is not a plausible performance profile for the better algorithm, so it was
treated as evidence of a bug rather than of a slow machine. It was: each firing
derived exactly one fact, so saturation needed one round per derived fact and
the least model was badly incomplete.

**Secondary bug found by the fix.** When the delta seed covers a rule's *only*
body literal, the join has zero levels and yielded `true` forever. Guarded, with
a regression test (`single_literal_rule_terminates_and_derives`).

**Lesson recorded.** Inverted benchmark results are diagnostic. A surprising
number in the wrong direction is more informative than a plausible one.

---

## DD-0012 — No memoisation in `resolve` (Stage 1)

**Hypothesis.** Caching resolved subterms would pay off, since the same
subterm recurs across a firing.

**Decision.** Deferred. `resolve` is iterative post-order with reusable vectors
and no cache.

**Reasoning.** The cache must be invalidated on every `undo_to`, and a
subtraction-based cache in a traversal-heavy path can cost more than it saves. A
`ResolveCache` type was written and then **deleted** rather than left as
speculative complexity. The measurement that would justify reintroducing it is
recorded as a benchmark to add.

---

## DD-0013 — No neural components

**Hypothesis.** A small heuristic network could improve branch ordering or
strategy selection.

**Decision.** None. §6 permits models under 1 M parameters; none are present.

**Reasoning.** §6 requires demonstrating benefit sufficient to justify memory,
inference cost, implementation complexity, and loss of determinism. On a
single core, a neural forward pass costs more than the symbolic heuristic it
would replace, for a heuristic that must then be *verified* anyway. The
requirement to justify a component before adding it is the operative one; the
honest answer today is that nothing has been shown to need it.

**Revisit when.** A symbolic heuristic is measured to underperform on a specific
benchmark family, and the neural alternative beats it reproducibly.

---

## DD-0014 — Proof recording is a switch, not a constant

**Hypothesis.** Recording a derivation per derived fact is cheap enough to leave
unconditional.

**Decision.** `ProofMode::{Full, Off}`, defaulting to `Full`.

**Reasoning.** Measured: a closure of 12.5 M facts cost 3.1 GB RSS — about
**248 B per fact** against roughly 19 B of IR payload. Each `Derivation` holds two
`Vec`s, each a separate heap block. Proof logging is not a tax on the algorithm;
it *is* the memory cost.

**Honesty preserved.** With `Off` the engine reports `Found`, not `Proved`,
because it has nothing to check. A definite status must never be emitted without
backing.

---

## DD-0015 — Monolith with modules, not a workspace

**Hypothesis.** Splitting into crates improves compile times and enforces
dependency direction.

**Decision.** One crate, strict module boundaries.

**Reasoning.** The development machine is 2 cores; a 6-crate workspace spends most
of its time on process startup and link steps rather than on type-checking. The
boundaries that matter — exterior versus core — are already enforced by
`pub`/`pub(crate)` and by the module table in `ARCHITECTURE.md` §4.

**Trigger to split.** Compile time exceeding ~60 s on the 2-core box, or a
genuine cycle between modules that needs naming.

---

## DD-0016 — Deterministic work budgets, never time budgets, in benchmarks

**Hypothesis.** Time-limited benchmarks are simpler.

**Decision.** Rejected. Benchmarks are bounded by `Budget::steps`, and time is
measured rather than used as a limit.

**Reasoning.** A wall-clock cutoff makes the amount of computation
machine-dependent, so two runs on the same machine are not comparable and none
of the algorithmic comparisons are meaningful. `Budget` still supports a time
limit for interactive use, and two benchmarks deliberately study budget
exhaustion — but they report deterministic counters alongside.

---

## DD-0017 — Untracked: `Predicate::idb` includes fact-only predicates

**Status.** Accepted, documented, not a bug.

**Observation.** A predicate defined only by facts is still marked IDB, because
it is the head of rules with empty bodies. Bottom-up evaluation therefore treats
it as delta-seeded rather than static.

**Consequences, all correct:** such predicates participate in the delta rather
than being evaluated once as static rules; `idb_fact_count` counts them; and a
single-literal rule over one reaches the zero-level join path that DD-0011's fix
had to handle. Observed in benchmarks as `edge` contributing to `idb_facts`.
Recorded because the surprise cost real debugging time and will surprise the next
reader of the numbers.