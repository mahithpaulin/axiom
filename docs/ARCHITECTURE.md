# ARCHITECTURE

This document describes the root `axiom` crate and its relation to the v4
workspace. The v4-specific architecture, including ASP, FOL, planning, the proof
kernel, and the router, is in [`v4/ARCHITECTURE.md`](v4/ARCHITECTURE.md).

## 1. Thesis

There is no single logic that covers Datalog, ASP, first-order refutation,
SAT modulo theories, and planning. The project therefore uses one **contract**
and several **engines**, not one universal formula type:

```text
Problem ──▶ Engine::solve ──▶ Outcome { Verdict, Evidence }
                                      │
                                      ▼
                              Engine::verify
```

The contract lives in `crates/axiom-core`. Each engine owns its syntax and
semantics. This avoids pretending that, for example, closed-world Datalog
negation and ASP default negation are the same operation.

## 2. Root crate layers

```text
surface text (src/exterior.rs)
        │
        ▼
hash-consed terms / atoms / rules (src/term.rs, src/program.rs)
        │
        ├── forward least model (src/solver_fwd.rs)
        ├── backward SLD (src/solver_bwd.rs)
        ├── proofs and checking (src/proof.rs, src/check.rs)
        ├── CDCL SAT (src/sat.rs)
        ├── CDCL(T) RDL + UF (src/theory.rs)
        └── V2 representations (src/repr.rs, csp, state, search, games)
```

The exterior is the only place with source-level domain knowledge. The core
operates on interned symbols and arena terms. Terms are `u32` ids; the arena is
hash-consed.

## 3. Root module map

| Module | Role |
|---|---|
| `symbol` | name interning |
| `term` | hash-consed term/atom arena |
| `subst` | union-find unification with occurs check and trail |
| `db` | extensional database with two index levels |
| `program` | rules, literals, stratification, builder |
| `solver_fwd` | semi-naive forward evaluation and stratified negation |
| `solver_bwd` | depth-bounded SLD for `prove` and `query` |
| `proof`, `check` | derivation records and independent replay |
| `sat` | two-watched CDCL, learning, restarts, RUP certificates |
| `theory` | DPLL(T) over RDL and congruence closure |
| `csp`, `puzzle` | finite-domain propagation with explanations |
| `state`, `domains` | explicit-state planning and BMC lowering |
| `search` | A*, IDA*, alpha-beta over explicit graphs/trees |
| `chess`, `chess_play`, `go` | bounded game move generation and play |
| `choose` | deterministic chooser among V2 paths |
| `bench` | timing/allocation harness (RSS column is post-solve) |
| `budget`, `status` | resource limits and the honesty contract |

## 4. Datalog semantics in the root crate

- Stratified Datalog over finite terms.
- The forward engine computes the least model; evaluation is semi-naive.
- A negated literal succeeds only when fully ground and absent. If it never
  becomes ground, the derivation is blocked. Programs are expected to be safe;
  unsafe programs are incomplete rather than reinterpreted.
- B3 (fixed in v4) was an ordering bug: negation was tested before later
  positive literals bound its variables. The check now runs after the positive
  joins.
- Function symbols in rule heads make a rule `backward_only`; forward
  saturation does not enumerate an infinite Herbrand universe.
- `Refuted` requires a completed least model, not a depth or budget decline.
  Declines are `Unknown`/`Exhausted`.

## 5. SAT and theory

`src/sat.rs` is a CDCL solver with two-watched propagation, first-UIP learning,
VSIDS, phase saving, Luby restarts, and learned-clause deletion. Models are
checked by satisfaction; UNSAT is checked by reverse unit propagation.

`src/theory.rs` is a DPLL(T) driver over:

- integer difference constraints `x - y ≤ c`;
- equality/disequality over uninterpreted terms;
- congruence closure;
- Nelson–Oppen combination of the two.

Theory lemmas carry hypotheses; `verify_theory_unsat` replays them together
with the propositional RUP proof. `verify_theory_sat` re-asserts the model and
checks consistency. There is no general linear arithmetic, real arithmetic,
arrays, bitvectors, strings, quantifiers, or incremental push/pop.

## 6. Status contract

Root `Status` and v4 `Verdict` use different vocabularies but the same rule:

- a definite answer carries evidence;
- an inconclusive answer carries none;
- inconclusive is never a negative answer.

`ProofMode::Off` produces `Found` rather than `Proved` because there is nothing
to check. Planning `Impossible` is only emitted after exhaustive finite search,
never after a cap.

## 7. Verification

`Solver::verify` re-derives a goal from facts and rules without the solver's
substitution, arena, or join. `tests/reference.rs` is a second implementation
(string terms, naive fixpoint, no index) used for differential testing. SAT and
theory have separate checkers.

v4 engines use serialised evidence and per-engine verifiers. See
[`v4/VERIFICATION.md`](v4/VERIFICATION.md) for the exact checks and trust
assumptions.

## 8. Performance posture

Measured on the root crate:

- 16 bytes per term node; duplicate interning allocates nothing;
- first-argument index examines 495.8× fewer tuples than a scan;
- transitive-closure candidate growth slope ≈ 2.00 over `n = 100..800`, with
  zero unbound scans;
- ~324 B RSS per derived fact with proofs, ~197 B without.

Memory is the cost. The kernel RSS column is sampled after the solver drops and
is not peak memory (`src/bench.rs:206-258`, F-03). Only the in-closure memory
probe is valid for per-fact memory claims.

## 9. Non-goals

- one IR that hides semantic differences between engines;
- competitive parity with specialist solvers;
- formal verification of the implementation;
- external solver dependencies in the runtime;
- distributed or GPU execution;
- claims unsupported by checked evidence.
