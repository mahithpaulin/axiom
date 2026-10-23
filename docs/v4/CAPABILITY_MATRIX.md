# Axiom v4 — capability matrix

Audit date: 2026-10-21
Baseline: `main` @ `4c60f3f` (tag `v4-baseline`); status updated for branch `v4`.
Matrix owner: this file. Narrative docs that disagree are stale until
reconciled (see `AUDIT.md` F-01).

## Legend

| Label | Meaning |
|---|---|
| **Implemented** | Working code in `v4`, exercised by at least one named test, for the fragment it documents. |
| **Partial** | Working subset, or a documented incompleteness / missing sub-capability. |
| **Planned** | No code in `v4`; assigned to a future stage. |
| **Broken** | Code exists but a known defect makes the stated capability unreliable; a regression test is the first fix. |
| **Absent** | No code and not currently scheduled in the v4 plan. |

“Evidence” cites source and, where possible, the test or CI observation. A
capability is not upgraded from Partial/Planned because a document claims it.

## Summary

| Engine family | v4 status |
|---|---|
| 1. Axiom foundation (Datalog, SAT, V2) | implemented with scoped limits; B3 scheduling fixed |
| 2. SMT / constraints (Z3 reference) | RDL + UF over CDCL(T), with an SMT-LIB 2 subset frontend |
| 3. High-performance Datalog (Soufflé reference) | partial: correct, not competitive |
| 4. ASP (clingo reference) | implemented finite fragment with model validation |
| 5. First-order proving (Vampire reference) | implemented bounded resolution; ground equality normalization plus non-ground equality axioms; no superposition or `Refuted` |
| 6. Trusted proof kernel (Lean 4 reference) | small resolution kernel + STLC checker; not formally verified |
| 7. Planning / heuristic search (Fast Downward reference) | untyped STRIPS with A* `h_max`; root StateGraph retained |
| 8. v4 common infrastructure | implemented `Engine`/evidence/registry contract; external harness added |
| 9. Cross-domain router | implemented dispatch + per-engine verification; one checked ASP→planning bridge |

Counts were removed because they invited scorekeeping. Several “implemented”
rows are narrow fragments with explicit boundaries.

---

## Engine 1 — Axiom foundation

| Capability | Status | Evidence | Notes / boundary |
|---|---|---|---|
| Symbolic representation: symbols, hash-consed terms, atoms, rules | Implemented | `src/symbol.rs`, `src/term.rs`, `src/program.rs`, `src/repr.rs`; 64 lib tests | Untyped first-order terms; no sorts. |
| Datalog facts, rules, positive recursion | Implemented | `src/solver_fwd.rs:438`, `src/program.rs`; `tests/soundness.rs`, `tests/v2.rs` | Least model over the finite positive fragment. |
| Semi-naive evaluation | Implemented | `src/solver_fwd.rs:438`; `diag` job (2 rounds, exact closure) | Mixed all-old/all-new delta; no per-rule variant selection. |
| Recursive inference with function symbols in heads | Partial | `src/program.rs` `backward_only`, `src/solver_bwd.rs`; §B4/§B5 | Ground goals, positive bodies, depth 64; saturation skips these rules. |
| Stratified negation | Partial | `src/program.rs` safety check; `src/solver_fwd.rs:98-116`; `tests/soundness.rs::negation_waits_for_later_positive_bindings` | B3 scheduling fixed. Unsafe forward rules are rejected. `backward_only` rules keep the older incomplete-negation contract. |
| Negation-as-failure / unstratified negation | Absent | `src/program.rs` rejects negative cycles; `docs/LANGUAGE_SPEC.md` §8 | Deliberate: a unique least model is required for `Refuted`. |
| Efficient relations / indexing | Partial | `src/db.rs:41-44,128`; `diag` job | Hash indexes on argument positions 0 and 1 only; no cardinality-aware join order. |
| Join ordering / query planning | Absent | `docs/ROADMAP.md` II7 | Body order is source order. |
| Provenance / explanations | Partial | `src/proof.rs`, `src/solver.rs:268`, `src/check.rs`; `tests/soundness.rs` | Derivation chains, not provenance semirings. `ProofMode::Off` downgrades to `Found`. |
| Least-model completeness / honest status | Partial | `src/status.rs`, `src/solver_bwd.rs`; `tests/soundness.rs` | A1/A2/A9 fixed; B3 scheduling fixed. `Impossible` is not produced by Datalog. |
| SAT core (CDCL) | Implemented | `src/sat.rs:11-12`; `tests/sat.rs` | Two-watched literals, first-UIP, VSIDS, phase saving, Luby restarts, learned-clause deletion. |
| Conflict analysis / learned clauses | Implemented | `src/sat.rs:465-645`; `tests/sat.rs` | Learned clauses retained in a RUP proof stream. |
| Model generation and validation | Implemented | `src/sat.rs:837`, `src/solver.rs:268`, `src/check.rs` | SAT models checked by satisfaction; Datalog derivations replayed. |
| Unsat certificate generation / checking | Implemented | `src/sat.rs:920`, `src/theory.rs:1152`; `tests/sat.rs` | RUP check is independent of the solver's propagation code. No DRAT export yet. |
| Puzzles: sudoku, N-queens, map colouring, logic grids | Implemented | `src/puzzle.rs:13,67,91,105`, `src/csp.rs:785`; `tests/v2.rs` | Finite-domain CSP, not a general constraint language. |
| Search: Dijkstra / A* / IDA* / alpha-beta | Implemented | `src/search.rs:98,159,334`, `src/state.rs:128`; `tests/v2.rs` | Explicit graphs/trees; no PDDL and no learned heuristics. |
| Planning: explicit state graph, optimal cost, BMC lowering | Partial | `src/state.rs:128,209`, `src/domains.rs`; `tests/v2.rs`, `examples/plan.rs` | Actions are graph edges (`from`, `to`, `cost`), not preconditions/effects. |
| Plan validation | Implemented | `src/state.rs:110`; `tests/v2.rs` | Replays the action names and checks the cost. |
| Chess: legal movegen, FEN, perft, mate-in-one | Implemented | `src/chess.rs:443,493,815,838`; `tests/v2.rs` | Perft 20/400/8902; no strength or optimality claim. |
| Chess: fixed-depth play, draw rules | Implemented | `src/chess_play.rs:209,287`; `tests/chess_play.rs` | Heuristic, depth-bounded; not a strong engine. |
| Go: liberties, captures, ko, capture-in-one | Partial | `src/go.rs:174,190`; `tests/v2.rs` | 5×5-oriented; no scoring, no full-board play. |
| Deterministic solver selection | Implemented | `src/choose.rs:86`; `chooser_is_deterministic` | Only plans choose between Dijkstra and bounded SAT; other representations map 1:1. |
| MCP integration | Absent on `main` | `v3-slice-1` branch, `crates/axiom-mcp` | Unmerged PR #7. Std-only stdio JSON-RPC; needs rebase/review. |
| TUI integration | Absent on `main` | `v3-slice-1`, `crates/axiom-tui` | Unmerged; pulls external crates (ratatui etc.). Not part of the core. |

---

## Engine 2 — SMT and constraint reasoning (Z3 reference)

Supported fragment on `main`: **quantifier-free Boolean combinations of
integer difference constraints `x - y ≤ c`, equality/disequality over
uninterpreted terms, congruence closure, and Nelson–Oppen combination**, solved
by a DPLL(T) driver over the existing SAT core.

| Capability | Status | Evidence | Notes / boundary |
|---|---|---|---|
| Boolean formulas + SAT integration | Implemented | `src/theory.rs:969-1081`, `src/sat.rs:692`; `tests/theory.rs` | Theory atoms are abstracted to SAT variables; lemmas are emitted on conflict. |
| Equality reasoning + congruence closure | Implemented | `src/theory.rs:284-510`; `tests/theory.rs::uf_propagates_congruence_through_lemmas` | No E-matching; congruence over indexed ground terms. |
| Integer difference logic | Implemented | `src/theory.rs:24-283`; `tests/theory.rs::rdl_*` | Exact negation: `¬(x-y≤c)` = `y-x≤-c-1` over integers. |
| General linear integer arithmetic | Absent / Planned Stage 4 | — | No Simplex, no bounds beyond difference constraints. |
| Real arithmetic | Absent | — | Integer-only encoding. |
| Theory propagation and conflict explanations | Implemented | `src/theory.rs:735-948`, `TheoryLemma`; `verify_theory_unsat` | Each lemma carries hypotheses; the checker replays them. |
| Incremental solving / assumptions / push-pop | Absent | `src/theory.rs:966-975` | Driver is single-shot per formula. |
| Model construction and validation | Implemented | `src/theory.rs:1309` `verify_theory_sat` | Re-asserts the model's atoms and checks consistency. |
| Unsat evidence | Implemented | `src/theory.rs:1152` `verify_theory_unsat`; `tests/theory.rs` | Propositional RUP plus theory-lemma replay. |
| Optimization (minimize/maximize, MaxSMT) | Absent | — | Planned after the decision fragment is reliable. |
| SMT-LIB parser | Implemented (subset) | `crates/axiom-smt/src/parse.rs` | `set-logic`, `declare-fun`, `declare-const`, `assert`, `check-sat`, `push`, `pop`; Int/Bool sorts; quantifier-free difference logic with uninterpreted functions. No printer. |
| SMT sessions | Implemented | `crates/axiom-smt/src/lib.rs` | One answer per `check-sat`, each with its own certificate. Every check is solved from scratch: no clause or theory-state reuse. |
| SMT-LIB conformance | Absent | — | No external conformance suite; the differential harness checks five hand-written fixtures against Z3. |
| Arrays, bitvectors, strings, quantifiers | Absent | — | Explicitly outside the current fragment. |
| Differential testing against Z3 | Partial | `benchmarks/external/run.py` | Test-only oracle; no runtime dependency. Two pigeonhole SAT cases and five SMT-LIB cases. |

---

## Engine 3 — High-performance Datalog (Soufflé reference)

| Capability | Status | Evidence | Notes / boundary |
|---|---|---|---|
| Semi-naive recursive evaluation | Implemented | `src/solver_fwd.rs:438`; `diag`, `tests/soundness.rs::naive_and_semi_naive_agree_on_transitive_closure` | Same algorithm family as Soufflé; small differential fixture added in `benchmarks/external/`. |
| Multiple relation indexes | Partial | `src/db.rs:41-44` | Positions 0 and 1; later positions scan. |
| Join ordering / cardinality-aware planning | Absent / Planned Stage 5 | — | Source order only. |
| Efficient tuple storage | Partial | `src/term.rs` (16 B/node), `src/db.rs`; `memory_per_fact_probe` | 20 B IR payload/fact; ~324 B RSS/fact with proofs, ~197 B without. |
| Duplicate suppression | Implemented | `src/db.rs` insertion path | Hash-consing plus predicate membership. |
| Stratified negation | Partial | `src/program.rs`; `src/solver_fwd.rs:98-116` | Scheduling and safe-rule rejection fixed; backward-only rules remain outside the safe fragment. |
| Provenance / derivation explanations | Partial | `src/proof.rs`, `src/check.rs` | Full derivation records when `ProofMode::Full`; no provenance semiring. |
| Memory-efficient storage / peak measurement | Partial | `src/bench.rs`; `tests/bench_metrics.rs` | `Bench::run` and `run_once` now record `VmHWM` (`peak_rss_kb`), matching the A/B path. The value is process-wide, so it is not a per-row delta. |
| Parallel evaluation | Absent | — | Single-threaded. |
| Soufflé differential benchmarks | Partial | `benchmarks/external/run.py`; `external-bench.yml` | One transitive-closure and one safe-negation program (two queries); not a corpus or performance claim. |
| Magic sets / demand transformation | Absent | `docs/ROADMAP.md` II7 | Planned compiler pass. |
| Rule subsumption / argument reordering | Absent | `docs/ROADMAP.md` II7 | Only constant folding and dead static rules exist today. |

---

## Engine 4 — Answer Set Programming (clingo reference)

| Capability | Status | Evidence | Notes / boundary |
|---|---|---|---|
| ASP input representation | Implemented | `crates/axiom-asp/src/syntax.rs` | Facts, normal rules, choice rules, constraints, `#show`. No aggregates/functions. |
| Grounding | Implemented (naive) | `ground.rs`; `MAX_UNIVERSE=22`, `MAX_GROUND_RULES=200_000` | Full assignment of safe variables over constants; correct but not a real grounder. |
| Choice rules | Implemented | `stable.rs::choice_is_optional` | Selected heads seeded only when the body holds. |
| Integrity constraints | Implemented | `stable.rs::unsat_constraint_is_impossible_only_after_complete_enumeration` | A satisfied constraint rejects the candidate. |
| Stable-model semantics | Implemented | `stable.rs::is_stable`, `validate_model` | Reduct closure equality; empty model for positive loops. |
| Search and propagation | Partial | `stable.rs::enumerate` | Exhaustive subset enumeration; no learning or propagation. |
| Conflict-driven learning | Absent | — | Not attempted. |
| Answer-set enumeration | Implemented with cap | `Enumeration { complete }` | 22-atom universe; default 1024 models; truncation is explicit. |
| Independent answer-set validation | Implemented | `AspEngine::verify` | Re-grounds, re-enumerates, validates every model. Shares `is_stable`. |
| aggregates/cardinality/optimisation | Absent | parser rejects | Explicit `Unsupported`/parse error. |

---

## Engine 5 — Automated theorem proving (Vampire reference)

| Capability | Status | Evidence | Notes / boundary |
|---|---|---|---|
| FOL syntax | Implemented | `crates/axiom-prover/src/fol.rs` | Quantifiers, Boolean connectives, predicates/functions, infix equality. No sorts/arithmetic. |
| Variable scope and capture avoidance | Implemented | NNF alpha-renaming, Skolemisation | `cnf.rs`; tested on small formulas. |
| Clausal form | Implemented | `cnf.rs` | NNF, Skolem, CNF with deterministic naming. |
| Resolution and factoring | Implemented bounded | `resolve.rs`; `Limits` | Given-clause, factoring, tautology/subsumption checks. |
| Clause selection/search strategies | Partial | `resolve.rs` | Simple deterministic selection; no portfolio or sophisticated heuristics. |
| Equality | Partial | `fol.rs::normalize_ground_equality`, `Signature::equality_axioms` | Ground equalities use congruence closure; non-ground equality uses reflexivity/symmetry/transitivity/congruence axioms. No superposition/paramodulation. |
| Simplification/redundancy | Partial | tautology + subsumption | No rewrite/term indexing beyond simple checks. |
| Proof production | Implemented | `axiom-fol-resolution` evidence | S-expression resolution proof. |
| Independent proof checking | Implemented | `axiom-proof::check_resolution` | Re-runs unification and clause construction. |
| Completeness claims | None | saturation → `Unknown` | General FOL validity is undecidable; caps are explicit. |

---

## Engine 6 — Trusted proof kernel (Lean 4 reference)

| Capability | Status | Evidence | Notes |
|---|---|---|---|
| Small trusted kernel | Implemented | `crates/axiom-proof/src/lib.rs` | Resolution/refutation kernel; no typed logical framework. |
| Explicit proof terms | Implemented for resolution | `ProofClause`, `StepRule`, `ResolutionProof` | Serialisable S-expressions. |
| Typed expressions and contexts | Implemented for STLC | `stlc.rs` | Base/arrow/product types; no dependent types. |
| Type checking | Implemented | `infer_type`, `check_type` | Typing only, not consistency. |
| Common evidence IR | Partial | `axiom_core::Evidence` | Text kind/payload; no typed evidence schema. |
| Separation of search from verification | Implemented | `Engine::verify` per crate | FOL, ASP, planning, Datalog each re-check. |
| Kernel integration for solver outputs | Implemented for FOL only | `FolEngine::verify` | ASP/planning use their own validators. |
| Formal-verification claim | None | — | Do not claim. |

---

## Engine 7 — Planning and heuristic search (Fast Downward reference)

| Capability | Status | Evidence | Notes / boundary |
|---|---|---|---|
| Finite state representation | Implemented | root `src/state.rs`; `axiom-planning` | Root graph and STRIPS state sets. |
| Declarative actions | Implemented (STRIPS) | `crates/axiom-planning/src/pddl.rs` | Untyped STRIPS; negative preconditions/delete effects. |
| Initial state and goals | Implemented | `pddl.rs`, `planner.rs` | Conjunctive goals only. |
| Breadth-first baseline | Implemented | `planner::plan` | Shortest in action count; direct-call compatibility. |
| A* / admissible `h_max` | Implemented | `planner::plan_with`, `h_max` | Wired into `axiom-planning`; default engine search; shortest plans. |
| Duplicate-state detection | Implemented | `planner.rs` visited set | Deterministic. |
| Plan reconstruction | Implemented | `Plan` action sequence | — |
| Independent plan validation | Implemented | `validate_actions` | Replays from initial state; shares transition code. |
| Budgets/interruption | Implemented | step budget + state/action caps | Caps are `ResourceLimit`. |
| PDDL parser | Partial | `pddl.rs` | Small subset; not conformant PDDL. |
| Typing/equality/numeric/costs | Absent | parser rejects | Explicit `Unsupported`. |

---

## Engine 8 — v4 common infrastructure

| Capability | Status | Evidence | Notes |
|---|---|---|---|
| Shared problem/result model | Implemented | `crates/axiom-core/src/lib.rs` | `Problem`, `Verdict`, `Evidence`, `Outcome`, `Stats`. |
| Typed IR with serialisation | Implemented (v4 subset) | `crates/axiom-ir` | Structural IR + Sexp; not root-arena serialisation. |
| Capability declarations | Implemented | `Engine::capabilities` | Name, version, kinds, fragments, guarantees, limits. |
| `solve(problem, budget)` interface | Implemented | `Engine::solve` | Adapters for four domains. |
| `verify(problem, result)` interface | Implemented | `Engine::verify` | Each engine has its own checker. |
| Resource budgets | Implemented (steps; wall clock observational) | `axiom::Budget` | No cancellation token. |
| Structured errors | Implemented | `VerifyError`, `RouteError`, `KernelError` | Per-layer, not one universal error enum. |
| Stable evidence serialisation | Partial | text payloads | No versioned schema. |
| Versioned internal API | Partial | workspace crate versions | No semver policy for unpublished crates. |
| Conformance/test harness | Partial | per-crate tests + CI; `benchmarks/external/` | Three small differential rounds; not conformance. |
| Benchmark suite | Partial | root benches + CI; `benchmarks/external/` | Differential suite exists; no scaling study yet. |
| Cross-domain router | Implemented (dispatch) | `crates/axiom-router` | First-registered-wins; no translation. |
| Checked ASP→planning bridge | Implemented (one pipeline) | `crates/axiom-bridge` | Selected validated model becomes extra `:init`; plan is replayed against translated task. |
| MCP/TUI adapters | Absent on `v4` | `v3-slice-1` branch | Unmerged; not part of v4. |

---

## Cross-domain demonstrations

| Demonstration | Status | Note |
|---|---|---|
| Datalog result checked by the theory engine | Not implemented | No constraint extraction API. |
| SAT + bounded planning | Root `StateGraph` lowering only | Not wired to `axiom-planning`. |
| FOL proof checked by the trusted kernel | Implemented | `FolEngine::verify` + `check_resolution`. |
| Planning plan replayed by a validator | Implemented | `validate_actions`. |
| ASP model used as planning initial facts | Implemented | `axiom-bridge`; ASP and planning evidence both checked. |
| Router dispatches all four domains | Implemented | `Router::standard` + verification. |
| Cross-domain evidence translation | Partial | One typed ASP→PDDL translation; router still does not translate. |

## Additional specialist capabilities

Chess (implemented, bounded), Go (partial), puzzles (implemented), search
(A*/IDA*/alpha-beta, implemented), explicit-state planning + BMC (partial).
None is claimed competitive with a specialist engine.
