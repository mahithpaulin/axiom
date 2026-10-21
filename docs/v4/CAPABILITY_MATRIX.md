# Axiom v4 — capability matrix

Audit date: 2026-10-21
Baseline: `main` @ `4c60f3f` (tag `v4-baseline`)
Matrix owner: this file. Narrative docs that disagree are stale until
reconciled (see `AUDIT.md` F-01).

## Legend

| Label | Meaning |
|---|---|
| **Implemented** | Working code in `main`, exercised by at least one named test, for the fragment it documents. |
| **Partial** | Working subset, or a documented incompleteness / missing sub-capability. |
| **Planned** | No code on `main`; assigned to a v4 stage. |
| **Broken** | Code exists but a known defect makes the stated capability unreliable; a regression test is the first fix. |
| **Absent** | No code and not currently scheduled in the v4 plan. |

“Evidence” cites source and, where possible, the test or CI observation. A
capability is not upgraded from Partial/Planned because a document claims it.

## Summary

| Engine family | Implemented | Partial | Planned/Absent |
|---|---|---|---|
| 1. Axiom foundation (Datalog, SAT, V2) | 9 | 4 | 2 |
| 2. SMT / constraints (Z3 reference) | 5 | 1 | 5 |
| 3. High-performance Datalog (Soufflé) | 2 | 4 | 4 |
| 4. ASP (clingo) | 0 | 0 | 8 |
| 5. First-order proving (Vampire) | 0 | 3 | 6 |
| 6. Trusted proof kernel (Lean 4) | 1 | 2 | 5 |
| 7. Planning / heuristic search (Fast Downward) | 5 | 1 | 6 |
| 8. v4 common infrastructure | 1 | 4 | 6 |

The counts are a reading aid, not a score. Several “Implemented” rows are
narrow fragments with explicit boundaries.

---

## Engine 1 — Axiom foundation

| Capability | Status | Evidence | Notes / boundary |
|---|---|---|---|
| Symbolic representation: symbols, hash-consed terms, atoms, rules | Implemented | `src/symbol.rs`, `src/term.rs`, `src/program.rs`, `src/repr.rs`; 64 lib tests | Untyped first-order terms; no sorts. |
| Datalog facts, rules, positive recursion | Implemented | `src/solver_fwd.rs:438`, `src/program.rs`; `tests/soundness.rs`, `tests/v2.rs` | Least model over the finite positive fragment. |
| Semi-naive evaluation | Implemented | `src/solver_fwd.rs:438`; `diag` job (2 rounds, exact closure) | Mixed all-old/all-new delta; no per-rule variant selection. |
| Recursive inference with function symbols in heads | Partial | `src/program.rs` `backward_only`, `src/solver_bwd.rs`; §B4/§B5 | Ground goals, positive bodies, depth 64; saturation skips these rules. |
| Stratified negation | Partial | `src/program.rs:28-29`, `src/solver_fwd.rs:99-116`; §B3 | **Incomplete**: a non-ground negated literal blocks the derivation and can still lead to `Refuted`. F-02. |
| Negation-as-failure / unstratified negation | Absent | `src/program.rs` rejects negative cycles; `docs/LANGUAGE_SPEC.md` §8 | Deliberate: a unique least model is required for `Refuted`. |
| Efficient relations / indexing | Partial | `src/db.rs:41-44,128`; `diag` job | Hash indexes on argument positions 0 and 1 only; no cardinality-aware join order. |
| Join ordering / query planning | Absent | `docs/ROADMAP.md` II7 | Body order is source order. |
| Provenance / explanations | Partial | `src/proof.rs`, `src/solver.rs:268`, `src/check.rs`; `tests/soundness.rs` | Derivation chains, not provenance semirings. `ProofMode::Off` downgrades to `Found`. |
| Least-model completeness / honest status | Partial | `src/status.rs`, `src/solver_bwd.rs`; `tests/soundness.rs` | A1/A2/A9 fixed; B3 remains. `Impossible` is constructed by the planner but not by Datalog. |
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
| SMT-LIB parser / printer | Absent | — | Rust API only; no external conformance suite. |
| Arrays, bitvectors, strings, quantifiers | Absent | — | Explicitly outside the current fragment. |
| Differential testing against Z3 | Absent | — | Planned as a test-only oracle; no runtime dependency. |

---

## Engine 3 — High-performance Datalog (Soufflé reference)

| Capability | Status | Evidence | Notes / boundary |
|---|---|---|---|
| Semi-naive recursive evaluation | Implemented | `src/solver_fwd.rs:438`; `diag`, `tests/soundness.rs::naive_and_semi_naive_agree_on_transitive_closure` | Same algorithm family as Soufflé; not yet differential-tested. |
| Multiple relation indexes | Partial | `src/db.rs:41-44` | Positions 0 and 1; later positions scan. |
| Join ordering / cardinality-aware planning | Absent / Planned Stage 5 | — | Source order only. |
| Efficient tuple storage | Partial | `src/term.rs` (16 B/node), `src/db.rs`; `memory_per_fact_probe` | 20 B IR payload/fact; ~324 B RSS/fact with proofs, ~197 B without. |
| Duplicate suppression | Implemented | `src/db.rs` insertion path | Hash-consing plus predicate membership. |
| Stratified negation | Partial | `src/solver_fwd.rs:99-116`; §B3 | Incomplete for non-ground negation. |
| Provenance / derivation explanations | Partial | `src/proof.rs`, `src/check.rs` | Full derivation records when `ProofMode::Full`; no provenance semiring. |
| Memory-efficient storage / peak measurement | Partial | `src/bench.rs`; F-03 | Dedicated probe is valid; per-row RSS column is post-solve and invalid. |
| Parallel evaluation | Absent | — | Single-threaded. |
| Soufflé differential benchmarks | Absent / Planned Stage 5 | — | Must use identical datasets and semantics; Soufflé as test oracle only. |
| Magic sets / demand transformation | Absent | `docs/ROADMAP.md` II7 | Planned compiler pass. |
| Rule subsumption / argument reordering | Absent | `docs/ROADMAP.md` II7 | Only constant folding and dead static rules exist today. |

---

## Engine 4 — Answer Set Programming (clingo reference)

| Capability | Status | Evidence | Notes |
|---|---|---|---|
| ASP input representation | Absent / Planned Stage 6 | — | No ASP syntax or AST. |
| Grounding | Absent / Planned Stage 6 | — | No grounding module. |
| Choice rules | Absent / Planned Stage 6 | — | — |
| Constraints (integrity constraints) | Absent / Planned Stage 6 | — | — |
| Stable-model semantics | Absent / Planned Stage 6 | — | Datalog least-model semantics must not be reused as a substitute. |
| Search and propagation | Absent / Planned Stage 6 | — | The SAT core is a possible substrate, but no ASP encoding exists. |
| Conflict-driven learning for ASP | Absent / Planned Stage 6 | — | — |
| Answer-set enumeration | Absent / Planned Stage 6 | — | Must not claim completeness without a termination argument. |
| Independent answer-set validation | Absent / Planned Stage 6 | — | Required before any enumeration result is accepted. |

---

## Engine 5 — Automated theorem proving (Vampire reference)

| Capability | Status | Evidence | Notes / boundary |
|---|---|---|---|
| First-order terms and unification | Partial | `src/term.rs`, `src/subst.rs` (occurs check, trail) | Untyped, no quantifiers or clause representation; used by Datalog. |
| Variable scopes and capture-avoiding substitution | Partial | `src/subst.rs`, `src/program.rs` rule-local variables; `tests/soundness.rs::deep_backward_proof_with_fresh_variables_per_step` | Rule-local freshening exists; no general FOL binder scoping. |
| Logical normalization / clausal form | Absent / Planned Stage 7 | — | — |
| Resolution and factoring | Absent / Planned Stage 7 | — | Backward SLD is ground, positive, depth-bounded, and not resolution. |
| Clause selection and search strategies | Absent / Planned Stage 7 | — | — |
| Equality reasoning / superposition | Absent / Planned Stage 7 | — | The theory layer has congruence, not superposition. |
| Simplification / redundancy elimination | Absent / Planned Stage 7 | — | — |
| Proof production for FOL | Absent / Planned Stage 7 | — | Datalog derivations are not FOL resolution proofs. |
| Independent proof checking | Partial | `src/check.rs`, `tests/soundness.rs` | Independent checker for Datalog derivations only. |
| Completeness claims | Absent | — | General FOL validity is undecidable; any implementation must state its calculus and search restrictions. |

---

## Engine 6 — Trusted proof kernel (Lean 4 reference)

| Capability | Status | Evidence | Notes |
|---|---|---|---|
| Small trusted kernel | Absent / Planned Stage 8 | — | No typed kernel. |
| Explicit proof terms | Partial | `src/proof.rs` (`Proof`, `Derivation`, `Saturation`), `src/sat.rs` (`UnsatProof`) | Evidence objects exist, but they are ad-hoc per engine, not a typed calculus. |
| Typed expressions and contexts | Absent | — | Terms are untyped `TermId`s; no sorts or contexts. |
| Type checking / definitional equality | Absent | — | — |
| Structured proof objects | Partial | `Proof`, `TheoryProof`, `CspOutcome`, `PlanOutcome` | Different shapes per engine; no common evidence IR. |
| Separation of search from verification | Implemented (per engine) | `src/check.rs`, `src/sat.rs:837,920`, `src/theory.rs:1152,1309`, `src/state.rs:110`, `src/csp.rs:123` | Real and valuable, but not a general kernel. |
| Kernel integration for solver outputs | Absent / Planned Stage 10 | — | Requires a sound translation per logic; none exists. |
| Formal-verification claim for all results | Absent | — | Must never be inferred from the existence of these checkers. |

---

## Engine 7 — Planning and heuristic search (Fast Downward reference)

| Capability | Status | Evidence | Notes / boundary |
|---|---|---|---|
| Finite state representation | Implemented | `src/state.rs:32-65` | Explicit state ids. |
| Actions with preconditions and effects | Partial | `src/state.rs:23-32` | Actions are compiled edges; no declarative preconditions/effects. |
| Initial state and goals | Implemented | `src/state.rs:40-64` | Single initial state; goal set. |
| Breadth-first baseline | Partial | `src/state.rs:128` | Dijkstra; unit costs reduce to BFS. |
| A* | Implemented (graph search) | `src/search.rs:98` | Available for explicit `SearchGraph`, not wired into `StateGraph` planning. |
| Greedy best-first | Absent | — | — |
| Duplicate-state detection | Implemented | `src/search.rs` closed set; `src/state.rs` `done` | — |
| Delete-relaxation / planning heuristics | Absent | — | No heuristic portfolio; `SearchGraph::set_heuristic` is caller-supplied. |
| Plan reconstruction | Implemented | `src/state.rs:128-190` | Predecessor chain. |
| Independent plan validation | Implemented | `src/state.rs:110`; `verify_plan` | Replays actions and cost. |
| Search budgets / interruption | Implemented | `src/budget.rs`; `PlanOutcome`/`Exhausted` | Step and wall-clock budgets; no external cancellation token. |
| Optimality on non-negative explicit graphs | Implemented | `src/state.rs:128` | Dijkstra terminates with `Impossible` only after full reachable exploration. |
| PDDL parser / grounded task language | Absent / Planned Stage 9 | — | — |
| Cost/resource-aware planning | Partial | `src/state.rs:32` | Edge costs and step budgets; no resource variables. |
| Optimal-plan certificates | Partial | `src/state.rs:128` | Dijkstra's exploration is the optimality argument; no separately checkable bound certificate. |

---

## Engine 8 — v4 common infrastructure

| Capability | Status | Evidence | Notes |
|---|---|---|---|
| Shared problem/result model | Partial | `src/repr.rs` (V2 only), `src/status.rs` | No cross-engine problem IR or evidence enum. |
| Typed IR with sorts / type checking | Absent / Planned Stage 2 | — | Terms are untyped. |
| Solver capability declarations (`capabilities()`) | Absent / Planned Stage 1 | — | — |
| `solve(problem, budget)` interface | Partial | Ad-hoc per module (`Solver`, `SatSolver`, `TheoryDriver`, `solve_csp`, `shortest_plan`, `astar`) | No common trait. |
| `verify(problem, result)` interface | Partial | Per-module verifiers, listed above | No common trait or evidence dispatch. |
| Resource budgets and cancellation | Implemented (steps/time) | `src/budget.rs`; `Exhausted::{Steps,Time,Depth,Memory,Malformed}` | No cancellation token or async interrupt. |
| Structured errors | Partial | `ParseError`, `CheckErr`, `SatCheckErr`, `TheoryError`, `Exhausted` | No unified error type across engines. |
| Stable serialisation | Absent / Planned Stage 2 | `docs/IR_SPEC.md` §10 | No JSON/binary/text IR dump. |
| Versioned internal API | Partial | crate version `0.1.0`; no semver policy for intermediate crates | v4 workspace must define it. |
| Shared conformance/test harness | Partial | `src/bench.rs`, per-suite tests | No cross-engine conformance harness or fixture format. |
| Benchmark suite | Partial | `benches/kernel.rs`, `sat.rs`, `theory.rs`, `v2perf.rs`; CI jobs | Strong per-engine microbenchmarks; no cross-engine or external-reference suite; RSS defect F-03. |
| Cross-domain coordinator | Absent / Planned Stage 10 | — | No dependency graph, no evidence translation, no origin tracking. |
| Deterministic router | Partial | `src/choose.rs` | V2 representations only; not capability/fragment based. |
| MCP/TUI adapters | Absent on `main` | `v3-slice-1` | Unmerged; see `BRANCH_ANALYSIS.md`. |

---

## Cross-domain demonstrations (Stage 10 targets)

None of these exist on `main`. They are listed here so they cannot be mistaken
for existing functionality.

| Demonstration | Status | Prerequisite |
|---|---|---|
| Datalog-derived constraints checked by the SMT engine | Planned Stage 10 | A constraint extraction API + SMT-LIB/IR adapter. |
| SAT + planning on a bounded planning problem | Partial foundation | `bmc_clauses` + SAT exist; no coordinator and no declarative planning task. |
| Prover proof validated by the trusted kernel | Planned Stages 7–8, 10 | FOL prover + typed kernel + sound translation. |
| Planner plan replayed by an independent validator | Implemented locally | `verify_plan` exists; the cross-domain composition does not. |
| ASP enumeration filtered by a constraint engine | Planned Stages 6, 10 | ASP engine + constraint API. |
| Symbolic policy rules + constraints justify a decision | Planned Stage 10 | Datalog + SMT/RDL adapters and evidence provenance. |

## Status of the “additional specialist capabilities”

All are audited above: chess (implemented, bounded), Go (partial), puzzles
(implemented), shortest path / A* / IDA* (implemented), planning + BMC
(partial), deterministic solver selection (partial). None is assumed to be
competitive with a specialist engine; no such benchmark exists yet.
