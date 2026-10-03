# ARCHITECTURE

## 1. The one-sentence thesis

**Problems are compiled into a single logical intermediate representation; a
portfolio of solvers reasons over that representation; every definite answer is
accompanied by a derivation that a separate checker re-verifies from the rules
alone.**

Everything else in this document is either a consequence of that sentence or a
measured correction to it.

---

## 2. Layers

```
                     EXTERNAL WORLD
                           │
                           ▼
             ┌───────────────────────────────┐
             │       LOGICAL EXTERIOR        │   domain knowledge lives here
             │  parse · encode · adapt       │
             │  state/action → rules         │
             │  answers → prose              │
             └───────────────┬───────────────┘
                             │  Program (the IR)
                             ▼
             ┌───────────────────────────────┐
             │         LOGICAL CORE          │   no domain knowledge at all
             │  representation (hash-consed) │
             │  unification · matching       │
             │  indexing · semi-naive eval   │
             │  resolution · proof checking  │
             └───────────────┬───────────────┘
                             │
              ┌──────────────┼──────────────┐
              ▼              ▼              ▼
        forward chain   backward res.   (later: CDCL(T), CP, search)
              └──────────────┼──────────────┘
                             ▼
              Status + Derivation + independent check
```

The boundary that matters is the arrow from the exterior to the core. Nothing
below it knows what a graph, a schedule, or a game is. §19's generality test is
exactly this: adding a domain costs an adapter, not a core change. Section 8
gives the evidence.

---

## 3. Why one IR does not mean one algorithm

The charter asks for a representation general enough to serve deduction,
constraints, search, planning, and mathematics, on one CPU, without a pile of
special cases. The naive reading — "one evaluator, one data structure" — is
wrong, and measurably so:

* A hash-consed term DAG is excellent for symbolic equality and unification, and
  poor for interval arithmetic, where a dense `f64` pair beats a pointer chase
  by more than an order of magnitude.
* A CDCL solver wants a flat array of literals, not a DAG.
* A constraint propagator wants a bitset domain, not a DAG.

So the IR is the **interchange format**, not the **executable form**. Each solver
lowers the IR into a representation it can execute quickly, and the charter's
own §9 anticipates this: "compile into a lower-level representation optimized for
execution." The compiler is real, it lives in `program.rs` and `solver_fwd.rs`,
and lowering is cheap relative to solving.

This is also the answer to the sharpest tension in the requirements: §3 demands a
compact, fast IR, and §12 demands coverage of constraint and numeric problem
families. Those pull apart. Resolving them by compromise gives an IR that is
adequate at everything. Resolving them by *specialising below the IR* gives an
IR that is merely the exchange rate between specialised solvers.

---

## 4. Module map

| Module | Responsibility | Domain knowledge |
|---|---|---|
| `hash` | Fast hasher for all internal tables | none |
| `symbol` | Interning; `u32` symbols after load | none |
| `term` | Hash-consed term/atom arena, 16 B/node | none |
| `subst` | Union-find unification, trail, resolution | none |
| `db` | Extensional database and indexes | none |
| `program` | Rules, literals, stratification, builder | none |
| `proof` | Derivation records, check errors | none |
| `check` | Independent proof checking | none |
| `solver*` | Engines and the public API | none |
| `exterior` | Surface syntax, tokeniser, parser | all of it |
| `bench` | Measurement harness | none |

`exterior.rs` is the only file allowed to know what a problem means. If a
concept from the outside world appears anywhere else, the architecture has been
violated and the test suite should say so.

---

## 5. Data flow, end to end

1. **Parse.** `exterior::parse` tokenises and builds a `Program`. Identifier case
   is preserved (lower-casing would silently convert every rule into a ground
   fact — a soundness bug, not a style choice). Every axis an attacker controls
   — token count, nesting depth, arity, rule count — is bounded and produces a
   `ParseError` with a position.
2. **Compile.** Names become interned symbol ids; terms become hash-consed arena
   nodes; variables become rule-local slots; rules are stratified by bound
   relaxation. Rules whose heads contain function symbols are marked
   `backward_only` because their relation is infinite.
3. **Execute.** `Solver::saturate` runs semi-naive bottom-up evaluation per
   stratum. `Solver::prove` tries that first and falls back to depth-bounded SLD.
4. **Record.** Each new fact gets a `Derivation`: rule id, the instantiation of
   that rule's variables, the resolved conclusion, and *all* resolved premises in
   body order.
5. **Check.** `Solver::verify` re-derives the goal using an implementation that
   shares no code with the solver — not the arena, not `Subst`, not the join.
6. **Report.** A `Status` that cannot distinguish "solved" from "gave up".

---

## 6. The status contract

This is the engine's most important honesty mechanism, so it is stated as an
invariant rather than a convention:

> A status that claims knowledge (`Proved`, `Refuted`, `Found`, `Impossible`)
> carries a proof object. A status that does not (`Exhausted`, `Unknown`) carries
> no proof, and callers must not read it as a negative answer.

Two consequences worth stating explicitly:

* **Undecidability is not a resource problem.** General first-order validity is
  undecidable; Church's theorem means no complete procedure exists for
  arbitrary quantified formulas. No amount of compute changes this. The engine
  therefore reports `Unknown` rather than pretending. (This mirrors the invariant
  adopted by the `z3rs` pure-Rust port of Z3: *soundness before completeness —
  a budget yields a sound `unknown`, never a wrong verdict*.)
* **`Refuted` has a specific meaning.** For bottom-up saturation it is "the atom
  is absent from the least model *and the least model was computed to
  completion*", and it is accompanied by a closure certificate: round count, IDB
  fact count, and an order-independent fingerprint of the whole closure. If
  saturation was cut short by a budget, the answer is `Exhausted`. This is
  enforced structurally — the certificate is only attached when `saturate`
  returned `Ok`.

The `ProofMode::Off` switch makes the same discipline visible from the other
side. With derivations disabled the engine *cannot* support a `Proved` claim, so
it reports `Found` — "a witness exists, no proof attached" — instead of a
definite status with nothing behind it.

---

## 7. What is actually complete, and what is not

Stage 1 implements **stratified Datalog**: facts, rules with positive and
stratified-negated bodies, function symbols in heads handled by resolution
rather than saturation, and complete least-model computation.

It is complete for that fragment. Outside it, it returns `Unknown` or
`Exhausted`. See `KNOWN_LIMITATIONS.md` for the itemised list, including two
that are genuine incompleteness rather than missing features:

* A negated body literal that is not fully instantiated **blocks** the
  derivation rather than being assumed true. Treating it as satisfied would
  derive facts classical negation does not license — soundness over
  completeness, deliberately.
* Backward resolution handles ground goals with positive bodies only. Negation
  and non-ground goals in backward mode are absent rather than approximated,
  because an incomplete version under the same status enum would be worse than
  no version.

---

## 8. The generality test

§19 asks that a new problem domain require only a new exterior adapter plus a
logical program. The evidence so far:

| Domain | Core changes required | Status |
|---|---|---|
| Graph reachability | none — two rules | works |
| Transitive closure | none — two rules | works |
| Logic-grid / scheduling (as Datalog) | none — rules + negation | works, `stratified_negation_5000` |
| Recursive functions in heads | none — same rules, backward engine | works |

The interesting one is the last. Adding an infinite-domain relation did **not**
require touching the inference engines' design; it required a flag at compile
time (`backward_only`) and a second engine that already existed. That is what
the architecture is for.

---

## 9. Performance posture

CPU-first, single-threaded by default, no GPU path, no runtime dependencies. The
representational choices are all in service of cache locality and predictable
allocation:

* 16 bytes per term node; a term is a `u32`; equality is an integer compare.
* Hash-consing gives structural sharing and makes the fact table a
  `HashSet<TermId>` rather than a set of vectors.
* All term traversals are iterative. A 200k-deep term is a test case, not a
  crash.
* Join backtracking uses reusable cursor and trail-mark stacks, so a rule firing
  allocates nothing for control state.

Measured numbers, the memory-attribution experiment, and the two algorithms
whose measurement contradicted my expectation are in `PERFORMANCE.md`. That last
point is the most useful thing in this document: semi-naive evaluation initially
appeared **350× slower** than the naive baseline, which is what exposed a
completeness bug in the join rather than a performance problem.

---

## 10. Explicit non-goals

Stated so they are not mistaken for gaps:

* **Not a complete theorem prover.** Full first-order refutation is out of scope
  for Stage 1 and would require a saturation-based engine with its own
  trade-offs.
* **Not an SMT solver.** No theory combination yet (ROADMAP II2 is next).
  The CDCL core itself is built (`src/sat.rs`): two-watched propagation,
  first-UIP learning, VSIDS, RUP-checked certificates. `z3rs` and
  `vampire-prover` were surveyed as prior art; both are dependencies
  this project declines, for the reason in `DESIGN_DECISIONS.md` (DD-0007).
* **No neural components.** §6 permits them under 1 M parameters. None are
  present, and none are justified yet: see DD-0013.
* **Not "solves any puzzle."** §24 of the charter already concedes this, and
  `KNOWN_LIMITATIONS.md` keeps the concession honest and itemised.