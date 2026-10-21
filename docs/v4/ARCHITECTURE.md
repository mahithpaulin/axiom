# Axiom v4 — architecture

Axiom v4 is a workspace of small engines behind one contract. The root `axiom`
crate remains the original zero-dependency symbolic engine; the `axiom-*`
crates add a common vocabulary, a Datalog adapter, ASP, a resolution prover, a
trusted proof kernel, STRIPS planning, and a cross-domain router.

This document describes what is actually wired. It is not a roadmap.

## 1. Design rule

> A definite verdict carries evidence; an independent verifier consumes the
> evidence and the original problem, not the search state that produced it.

Every engine exposes the same three operations:

```rust
fn capabilities(&self) -> Capabilities;
fn solve(&mut self, problem: &Problem, budget: &mut Budget) -> Outcome;
fn verify(&self, problem: &Problem, outcome: &Outcome) -> Result<(), VerifyError>;
```

`Problem` is source-level and engine-specific. `Outcome` is a `Verdict`, an
optional `Evidence { kind, payload }`, deterministic counters, and notes. The
contract is defined in `crates/axiom-core/src/lib.rs`.

## 2. Layers

```text
source text / domain input
        │
        ├── root axiom crate ── Datalog, SAT, CDCL(T), CSP, search, games
        │
        ├── axiom-asp ───────── finite grounding + stable-model enumeration
        ├── axiom-prover ────── FOL parse → NNF/Skolem → CNF → resolution
        ├── axiom-planning ──── untyped STRIPS → grounding → BFS → plan replay
        └── proof kernel ────── axiom-proof: resolution and STLC checks
                    │
              axiom-core contract + EngineRegistry
                    │
              axiom-router (standard bundle)
```

The arrows are dependencies, not data flow through a shared semantic IR. Each
engine owns its parser and semantics. This is deliberate: forcing ASP, FOL,
planning, SAT, and Datalog through one formula type would hide semantic
differences that the verifier must preserve.

## 3. Crates

| Crate | Role | Dependencies |
|---|---|---|
| `axiom` (root) | Existing Datalog/SAT/theory/CSP/search/game engine | none |
| `axiom-ir` | Typed structural IR and deterministic S-expression serialisation | none |
| `axiom-core` | `Problem`, `Verdict`, `Evidence`, `Engine`, `EngineRegistry`, Datalog adapter | `axiom` |
| `axiom-asp` | ASP syntax, finite grounding, stable-model search and validation | `axiom`, `axiom-core` |
| `axiom-proof` | Trusted resolution kernel and STLC type checker | `axiom-ir` |
| `axiom-prover` | FOL syntax, CNF, bounded resolution, FOL engine/verifier | `axiom-ir`, `axiom-proof`, `axiom-core` |
| `axiom-planning` | Untyped STRIPS PDDL, grounding, BFS planner, validator | `axiom`, `axiom-ir`, `axiom-core` |
| `axiom-router` | Standard engine bundle and verified routing | all four engines |

The root crate is still zero-dependency. Workspace crates use path
dependencies only; `Cargo.lock` remains gitignored as before.

## 4. Root engine (pre-v4)

The root crate is the mature part of the repository:

- stratified Datalog with semi-naive evaluation, two index levels, derivation
  proofs, and independent proof replay;
- a CDCL SAT core with RUP certificates;
- a quantifier-free CDCL(T) fragment over integer difference logic and
  congruence closure, with checked models and replayed theory lemmas;
- finite-domain CSP/puzzles, explicit-state planning (`StateGraph`), A*/IDA*/
  alpha-beta, and bounded chess/Go move generation.

v4 does not replace these. It wraps Datalog behind the common contract and
leaves the rest available through the root API. The old name `planning` for
`StateGraph` is retained; the new declarative planner is `axiom-planning`.

## 5. v4 data flow

### Datalog adapter

`Problem::datalog(source, goal)` is parsed by the existing exterior, solved by
the existing solver, and mapped from `Status` to `Verdict`. Verification
re-parses and re-solves with a fresh solver, compares the serialised evidence,
and checks the returned derivation proof. This is a second execution, not a
second implementation.

### ASP

`Problem::asp(source, max_models)` is parsed, grounded over the constants in the
program, and enumerated over the finite atom universe. Every candidate is
accepted only by the stable-model test. Evidence records the complete flag,
model count, counters, universe size, and models. Verification re-grounds,
re-enumerates with the same cap, compares evidence, and independently validates
each listed model.

### FOL

`Problem::fol(source)` is parsed into formulas. The goal is negated, the formula
set is converted to CNF with Skolemisation, and bounded given-clause resolution
runs. A refutation is serialised and checked by `axiom-proof::check_resolution`.
Verification additionally reconstructs the deterministic CNF and requires every
input clause in the proof to occur there.

### Planning

`Problem::planning(domain, problem)` is parsed as untyped STRIPS, grounded over
objects and constants, and searched with BFS. A plan is an action sequence.
Verification replays the plan from the initial state. `Impossible` verification
re-runs the exhaustive search; a cap hit is never treated as impossibility.

## 6. Verdict semantics

| Verdict | Meaning | Evidence required |
|---|---|---|
| `Proved` | A proof was produced and checked | Yes |
| `Refuted` | A definite negative result in a complete finite semantics | Yes |
| `Found` | A witness (model, plan, answer set) was produced | Yes |
| `Impossible` | A finite space was exhausted with no witness | Yes |
| `Unknown` | Search stopped without deciding | No |
| `Unsupported` | Input is outside the declared fragment | No |
| `ResourceLimit` | A deterministic or wall-clock budget stopped work | No |
| `Error` | Malformed input or an internal failure | No |

`Unknown`, `Unsupported`, `ResourceLimit`, and `Error` must never be read as
negative answers. The FOL prover never emits `Refuted`; absence of a found
refutation is not a countermodel. ASP emits `Impossible` only when enumeration
was complete and found zero stable models. Planning emits `Impossible` only
after exhaustive BFS within caps.

## 7. Trust boundaries

| Component | Trusted? | Why |
|---|---|---|
| `axiom-proof` kernel | Trusted base | Small; re-runs unification and clause construction |
| CNF/Skolem transformation | Prover-side | Tested, not formally verified; input clauses are checked against it |
| Root Datalog solver | Trusted implementation | Verifier re-executes the same code; proofs are replayed |
| ASP stable-model test | Trusted implementation | Same routine used by search and validation; negative tests exist |
| Plan replay | Trusted implementation | Re-executes the transition relation independently of BFS |
| Router | Thin | Only dispatches and calls each engine's own verifier |

No component claims formal verification. The kernel is a small independent
checker, not a proof of the Rust compiler, parser, or CNF converter.

## 8. Routing

`Router::standard()` registers, in order:

1. `DatalogEngine`
2. `AspEngine`
3. `FolEngine`
4. `PlanningEngine`

Routing is by `Problem::kind()`. First registered wins. `Router::solve` calls
the engine and then the engine's `verify` for every definite outcome. A failed
verification is returned as `RouterError::Verification`, never downgraded to an
inconclusive verdict. `solve_all` shares one budget and stops at the first
routing or verification error.

The router has no evidence translation and no cross-domain composition beyond
dispatching. A Datalog result cannot yet be fed into the SMT engine as a
constraint, and an ASP model cannot be filtered by a theory solver.

## 9. Determinism

All engines are single-threaded and deterministic for a fixed input and budget:

- ordered maps/sets are used for signatures, models, and evidence;
- clause and candidate order are deterministic;
- no hash-map iteration determines an answer;
- wall-clock limits exist, but deterministic step budgets are the primary cap.

Wall-clock `Stats::elapsed_ms` is observational and excluded from evidence.

## 10. Extension points

A new engine implements `Engine`, declares one `ProblemKind`, and documents its
fragment. It should:

- emit evidence only for definite verdicts;
- return `Unsupported` for out-of-fragment input rather than approximating;
- use a deterministic step budget;
- provide negative tests proving tampered evidence is rejected;
- avoid claiming completeness outside a finite or explicitly bounded search.

Until those hold, a new engine should not be registered in `Router::standard()`.
