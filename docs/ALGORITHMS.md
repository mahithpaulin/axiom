# ALGORITHMS

What is implemented, what it costs, and where it stops being correct. Each
section states the completeness boundary explicitly, per §11's requirement that
incompleteness be documented rather than implied.

---

## 1. Unification and matching

**Algorithm.** Union-find over term nodes with union by rank (variable↔variable
only), a trail for undo, and a mandatory occurs check. Martelli–Montanari–Pietrini
"efficient unification": binding `x` to `f(a)` is one pointer write and every
occurrence of `x` sees it.

**Complexity.** `find` is O(log n) in the worst case, O(1) in practice for
variable-only chains; term-to-term matching is O(size of term); the occurs check
is O(size of term), generation-stamped and allocation-free after warm-up.

**Link direction.** Fixed: a variable always attaches *under* a non-variable
(DD-0004). Plain union-by-rank would elect a variable as root after it accumulated
rank, making the binding invisible.

**No path compression** (DD-0005). Compression would need every rewrite trailed;
with it off, chains follow term nesting, which `resolve` walks anyway.

**Matching vs unification.** `match_into` binds only variables on the pattern
side; a variable on the fact side is `Clash`. This is the hot path in forward
chaining, where premises are matched against ground tuples.

**Known sharp edge.** The occurs check must not share the unification work stack
(DD-0003). It did, once, and silently bound only the first variable of every
compound literal.

---

## 2. Stratification

Bound relaxation over `max`: positive edges require `>=`, negative edges require
`>`. Handles positive cycles (transitive closure needs them) without an SCC pass.
Every stratum only ever increases and is bounded by the predicate count, so it
terminates; the build asserts convergence.

A negative edge that cannot be made strictly downward means no stratification
exists. The builder returns `NotStratified` instead of picking one.

---

## 3. Semi-naive bottom-up evaluation

**The algorithm.** A naive fixpoint re-runs every rule each round, so its cost is
quadratic in the number of derivations. Semi-naive computes only derivations whose
body includes at least one *new* fact — linear in the number of intermediate
tuples for the acyclic cases that matter.

**Variant.** *Mixed*: seed each body position in turn with the delta, join the
rest against the full relation. Most robust to rule shape, at the cost of
`|body|` firings per rule per round.

**Per firing:**
1. Match the seed literal (trail mark opened).
2. Check negated literals — see §3.1.
3. Repeatedly call `next_solution` until exhausted; for each solution, resolve the
   head and insert if new.
4. Undo to the trail mark.

**Join.** Resumable generator with per-level cursor and trail-mark stacks kept in
the solver, so a firing allocates nothing for control state. At each level the
candidate list is chosen by the first-argument index when that argument is bound.
Backtracking restarts a level from its saved cursor; depth is bounded by the body
length, so no input reaches the native stack.

**Why resumable.** An earlier non-resumable version returned only its last
solution, so each firing derived one fact and saturation needed one round per
derived fact (DD-0011). The benchmark suite exposed it as semi-naive appearing
350× slower than the naive baseline.

### 3.1 Negation

A negated literal blocks the derivation if it matches a stored fact **or** if it
is not fully instantiated.

The second clause is a **soundness** requirement, not an optimisation. Treating a
partially instantiated `not q(X)` as satisfied would derive facts that classical
negation does not license. The price is incompleteness for programs whose
negations never become ground — recorded in `KNOWN_LIMITATIONS.md`.

### 3.2 Completeness boundary

Complete **for stratified Datalog**. Not complete for:

* function symbols in heads — the relation is infinite (`backward_only`);
* negations that never become ground (see above);
* anything else the exterior cannot express.

---

## 4. Backward resolution (SLD)

Depth-bounded SLD for **ground** goals with **positive** body literals, with
failure memoisation keyed by `(goal, remaining depth)`.

**Why it exists.** `reach(succ(x))` has an infinite domain, so bottom-up
evaluation cannot enumerate it. Rather than special-casing infinite relations,
the same rules are handled goal-directed. This is the concrete case behind the
generality test: adding an infinite-domain relation needed a compile-time flag and
an engine that already existed, not a redesign.

**Deliberately absent.** Negation in backward mode, and non-ground goals. Both
are omitted rather than approximated: an incomplete version under the same status
enum is worse than no version, because a caller cannot tell which one it got.

**Terminability.** Bounded by `max_depth` (default 64) and the budget. A goal
proved only by exceeding the depth bound returns `Unknown`, not `Proved`.

---

## 5. Query answering

Non-ground goals are answered by matching against the saturated closure. Because
the closure is the least model and is computed completely, an empty answer set is
a **proof** that there are no answers, and is reported as `Refuted` with the
closure certificate attached. Each answer carries its own checkable proof.

---

## 6. Proof checking

Two strengths, deliberately separate:

| | Trusts | Cost | Status |
|---|---|---|---|
| `verify_shallow` | the forward chainer | O(1) | the goal is in the DB |
| `verify` | nothing but the rule set | O(proof size) | the default |

`verify` recursively re-derives the goal from program facts and rules, sharing no
code with the solver (DD-0010). For each derivation it checks that the
instantiation binds every rule variable exactly once to a ground term, that
applying it to the rule's head and body reproduces the recorded conclusion and
premises, that positive premises hold inductively, and that negated premises are
absent.

**Negative answers** commit to a closure fingerprint. The only way to support
"absent from the least model" is to show the least model was computed, so
`verify_saturation` compares a recomputed fingerprint. This relies on
determinism, which means a determinism bug surfaces as a *spurious check
failure* — the safe direction in which to fail.

---

## 7. Semi-naive versus naive: what was measured

Same program, same least model, `n = 600` path graph:

| | rounds | derivations | candidates | wall (3 iters) | allocs |
|---|---|---|---|---|---|
| semi-naive | see `PERFORMANCE.md` | | | | |
| naive fixpoint | | | | | |

The counters matter more than the wall time: a change that moves them changed the
*algorithm*; one that does not only moved a constant factor. The measured values
and the 13× memory attribution are in `PERFORMANCE.md`.

---

## 8. Not implemented

Named so their absence is unambiguous. Each has a ROADMAP entry:

* **SAT / CDCL** — implemented (`src/sat.rs`): two-watched propagation,
  first-UIP learning, VSIDS, phase saving, Luby restarts, activity-based
  detachment. Certificates both ways (models by satisfaction, unsat by RUP),
  frozen DIMACS corpus in `benches/data/`, cross-engine differential in
  `tests/sat.rs`.
* **CDCL(T) / theory combination** — linear integer/real arithmetic, congruence
  closure. Requires the SAT core first (now present).
* **Constraint propagation** — domains, propagators, MAC search, *explanation
  producing*. The explanation requirement is the interesting part: a propagator
  that removes a value without recording why cannot support a proof.
* **Search** — IDA\*, A\*, alpha-beta, transposition tables. Primitives for games
  and planning; the state-space lowering already exists for Datalog.
* **Symbolic mathematics** — polynomials, intervals, combinatorial identities.
* **Strategy selection** — the portfolio chooser. Pointless with one engine.
* **Partial evaluation** — the compiler passes in §9 of the charter are mostly
  unimplemented; only constant folding and dead-static-rule elimination exist.