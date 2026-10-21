# Axiom v4 — known limitations

This is the unflattering list. If a capability is not here, check
`docs/v4/CAPABILITY_MATRIX.md`; a document claim alone is not evidence.

## 1. Cross-cutting

- **External differential testing is new and narrow.** The
  `external differential benchmarks` workflow runs small SAT, ASP, Datalog,
  planning, and FOL fixtures against Z3, clingo, Soufflé, Fast Downward, and
  Vampire when those oracles are installed. It is not a conformance suite, an
  exhaustive benchmark corpus, or a performance claim. Missing oracles are
  reported as skipped, not as agreement.
- **No formal verification.** “Verified” means the outcome was re-checked by a
  Rust function. It does not mean a machine-checked metatheory.
- **Shared-code verification.** Datalog replay reuses the Datalog engine; ASP
  validation reuses the stable-model predicate; plan replay reuses the
  transition relation. A shared bug can pass both.
- **Evidence is not a stable format.** Payloads are text and may change without
  a compatibility guarantee.
- **Cross-domain composition is one checked pipeline.** `axiom-bridge` turns a
  verified ASP stable model into extra PDDL initial facts, then verifies the
  plan against the translated task. The router still only dispatches, and
  Datalog-to-theory, SMT filtering, and evidence translation are absent.
- **No cancellation token.** The prover checks a step budget at clause
  selection; long single steps are not pre-empted.
- **Wall-clock budgets are not reproducible.** They are best-effort; step
  counters are the reproducible limit.
- **GitHub Actions uses unpinned `stable`.** The declared MSRV 1.75 is not
  tested.
- **The root crate is still single-threaded and zero-dependency.**
- **RSS sampling is invalid for peak memory** (`src/bench.rs:206-258`, F-03).
  Do not use the kernel `rss kB` column as a peak baseline.

## 2. Datalog (`axiom-core::DatalogEngine`)

- Stratified Datalog only; negative cycles are rejected.
- Forward rules are now checked for Datalog safety: head variables and
  variables in negated literals must be bound by a positive body literal.
  Unsafe forward rules are rejected at build time instead of producing an
  incomplete closure. `backward_only` function-head rules retain the older
  contract and can still decline on unbound negation.
- Function symbols in rule heads are `backward_only`; they are not saturated.
- Backward resolution accepts ground goals, positive bodies, and a depth bound
  of 64. Non-ground subgoals and negation inside `backward_only` rules decline.
- `Status::Impossible` is reserved by the root API and not produced by the
  Datalog adapter.
- Verification re-executes the parser and solver; there is no independent
  Datalog proof checker beyond the existing derivation replay.
- No provenance semirings, join-order planning, magic sets, or parallel
  evaluation.
- SAT/theory/CSP/game capabilities are documented separately in
  `docs/KNOWN_LIMITATIONS.md`; they are not re-verified by v4.

## 3. ASP (`axiom-asp`)

- No function symbols, aggregates, cardinality bounds, optimisation,
  `#external`, or `#include`.
- Grounding assigns every safe variable over every constant. It does not
  perform joins or projection; it is correct for the finite fragment but
  exponentially wasteful.
- Enumeration is over all subsets of the ground universe: at most 22 atoms
  (4,194,304 candidates), 200,000 ground rules, and a 1024-model default cap.
- A capped enumeration returns `Found` with `complete=false`. The model list is
  real but the count is not complete.
- `Found` does not mean “all models found” unless `complete=true`.
- Search and validation share `is_stable`; there is no second stable-model
  implementation.
- No conflict-driven learning or propagation; the SAT core is not used.
- The `#show` directive is parsed but does not restrict the stored universe or
  evidence output beyond the implementation's normal handling.

## 4. FOL (`axiom-prover`)

- No equality, sorts, arithmetic, higher-order constructs, or type
  declarations. Equality is `Unsupported`.
- No `Refuted` verdict. A saturated search is `Unknown`; there is no
  countermodel or finite-model finder.
- Resolution is bounded: 4,096 clauses, 2,048 selected clauses, 8,192 generated
  clauses, plus the caller's step budget. Saturation is not a decision.
- Clause selection and indexing are simple; there is no goal-directed
  heuristics, superposition, or redundancy elimination beyond tautology and
  subsumption checks.
- The CNF/Skolem converter is trusted prover-side code. The kernel checks the
  refutation, not the transformation. A satisfiability-preserving bug in CNF
  could accept a wrong proof; tests are small and finite.
- The kernel trusts its input clauses. `FolEngine::verify` mitigates this by
  requiring every input to occur in the deterministic CNF, but both sides share
  the same converter.
- Proof text is a custom S-expression format, not TSTP/TPTP.
- The prover does not parse TPTP or SMT-LIB.

## 5. Planning (`axiom-planning`)

- Untyped STRIPS only. Typing, equality, numeric fluents, conditional effects,
  quantified/disjunctive goals, costs, and durative actions are rejected.
- No action costs: search minimises action count, not cost.
- The engine uses A* with an admissible delete-relaxation `h_max` heuristic by
  default; `planner::plan` retains breadth-first order for direct callers.
  State caps are 50,000 stored states and 100,000 expansions; ground actions
  are capped at 100,000.
- `Impossible` is only valid after exhaustive A* search within caps. A cap is
  `ResourceLimit`, never `Impossible`.
- Plan verification replays the same transition code used by search.
- PDDL parsing is a small S-expression subset; it is not a conformant PDDL
  parser and does not support all legal syntax for the advertised features.
- No plan optimality certificate beyond the admissible heuristic and exhaustive
  search argument.

## 6. Proof kernel (`axiom-proof`)

- The trusted base includes the S-expression parser, clause normalisation, and
  unification. It is small but not proved.
- The kernel does not check that input clauses are entailed by the problem;
  that is the engine verifier's job.
- The STLC checker covers types, arrows, products, application, and constants.
  It does not prove consistency, normalisation, or compiler correctness.
- No proof terms for Datalog, SAT, theory, ASP, or planning are translated into
  this kernel. Each engine keeps its own evidence format.
- No Lean/Coq formalisation.

## 7. Router (`axiom-router`)

- Dispatch only; first engine registered for a kind wins.
- No capability negotiation, cost model, fallback, or portfolio scheduling.
- A definite outcome from an engine is accepted only after that engine's
  verifier passes; there is no second engine cross-check.
- There is no evidence translation or provenance graph across domains.
- No persistence, caching, or incremental solving.

## 8. Root engine limitations retained

The root crate still has the issues catalogued in `docs/KNOWN_LIMITATIONS.md`,
including:

- the post-solve RSS measurement defect;
- no SMT-LIB parser;
- no general linear arithmetic or real arithmetic;
- no incremental/push-pop theory solving;
- no provenance semirings or magic sets;
- no external solver comparisons.

v4 did not fix these by renaming them.

## 9. Claims that must not be made

Do not claim, in a README, release note, or issue:

- “competitive with clingo/Vampire/Fast Downward/Z3”;
- “complete first-order theorem proving”;
- “formally verified”;
- “all ASP models” when `complete=false`;
- “unsatisfiable” for a FOL saturation;
- “impossible” for a planning cap;
- “verified peak memory” from the kernel RSS column;
- “cross-domain reasoning” beyond router dispatch.

The code and the evidence do not support those claims.
