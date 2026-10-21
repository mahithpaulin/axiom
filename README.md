# axiom — a multi-engine symbolic reasoning platform

Axiom is a Rust workspace of checked symbolic engines behind one contract. It
began as a zero-dependency Datalog/SAT engine and now adds answer-set
programming, first-order resolution, a trusted proof kernel, STRIPS planning,
and a router that verifies every definite answer.

```text
source problem
   │
   ├── Datalog ────── least model, proofs, SAT/Theory/CSP root engine
   ├── ASP ────────── finite grounding, stable models, model validation
   ├── FOL ────────── CNF, bounded resolution, kernel-checked refutations
   └── Planning ───── untyped STRIPS, A*/BFS, plan replay
             │
        axiom-core contract
             │
        axiom-router (dispatch + verify)
             │
        axiom-bridge (validated ASP -> planning)
```

## Quick start

Existing Datalog API (zero dependencies):

```rust
use axiom::{exterior, Budget, Solver, Status};

let src = "\
edge(a, b).
edge(b, c).
path(X, Y) :- edge(X, Y).
path(X, Z) :- path(X, Y), edge(Y, Z).
?- path(a, c).
";
let parsed = exterior::parse(src).unwrap();
let goal = parsed.queries[0];
let mut solver = Solver::new(parsed.program);
let mut budget = Budget::steps(1_000_000);
assert_eq!(solver.least_model(&mut budget).unwrap().idb_facts, 5);
let out = solver.prove(goal, &mut budget);
assert_eq!(out.status, Status::Proved);
assert!(solver.verify(&out.proof.unwrap()).is_ok());
```

v4 cross-domain API:

```rust
use axiom::Budget;
use axiom_core::Problem;
use axiom_router::Router;

let mut router = Router::standard();
let mut budget = Budget::steps(1_000_000);

// FOL: a proof checked by the resolution kernel.
let fol = Problem::fol("axiom P(a) -> Q(a). axiom P(a). goal Q(a).");
let out = router.solve(&fol, &mut budget).unwrap();
assert_eq!(out.outcome.verdict, axiom_core::Verdict::Proved);

// ASP: stable models, each independently validated.
let asp = Problem::asp("{ p }. :- p.", 0);
let out = router.solve(&asp, &mut budget).unwrap();
assert_eq!(out.outcome.verdict, axiom_core::Verdict::Found);
```

## What each engine decides

| Engine | Fragment | A definite answer means |
|---|---|---|
| Datalog (`axiom-core`) | stratified Datalog, finite terms, safe forward rules | least-model derivation or completed absence |
| SAT (`axiom::sat`) | propositional CNF | model checked by satisfaction; UNSAT by RUP |
| CDCL(T) (`axiom::theory`) | integer difference logic + equality/congruence | checked model or replayed theory lemmas |
| ASP (`axiom-asp`) | normal/choice rules, constraints, finite Herbrand grounding | each listed model passes the stable-model test |
| FOL (`axiom-prover`) | quantifiers, predicates, functions; no equality/arithmetic | kernel-checked empty clause |
| Planning (`axiom-planning`) | untyped STRIPS, negative preconditions, A* h_max | replayable shortest plan, or exhausted state space |
| STLC (`axiom-proof::stlc`) | simply typed lambda calculus | inferred type accepted by the checker |

Scoped limits are intentional. FOL saturation is `Unknown`, never `Refuted`.
ASP returns `Impossible` only for a complete zero-model enumeration. Planning
returns `Impossible` only after exhaustive search. A resource cap is
`ResourceLimit`, not a negative answer.

## The honesty contract

> A definite verdict carries evidence. An inconclusive verdict carries none and
> is not a negative result.

| Verdict | Evidence |
|---|---|
| `Proved`, `Refuted`, `Found`, `Impossible` | required and re-checked |
| `Unknown`, `Unsupported`, `ResourceLimit`, `Error` | absent by contract |

The router calls the producing engine's verifier before returning a definite
outcome. A verification failure is an error, not a downgraded verdict.

This is not formal verification. The FOL kernel is deliberately small, but the
CNF converter, root Datalog solver, ASP stable-model test, and plan transition
relation are trusted tested code. See `docs/v4/VERIFICATION.md`.

## Current verification status

GitHub Actions is authoritative. The Android/Termux device can run local
checks and release builds, but is not a CI substitute. Run `39596401907` on
branch `v4` passed all 10 jobs:

- 243 library/integration tests, 0 failed, 0 ignored;
- 7 doc tests;
- workspace `clippy -D warnings`, `fmt --check`, examples, and known-defects
  gates;
- existing kernel, SAT, theory, and scaling probes.

The B3 negation scheduling bug is fixed with a regression test. Forward rules
whose head or negated body variables are not bound by a positive body literal
are now rejected as unsafe; `backward_only` function-head rules retain their
separate contract. Details and run IDs are in `docs/v4/RELEASE_REPORT.md`.

## Repository layout

| Path | Contents |
|---|---|
| `src/` | root `axiom` crate: Datalog, SAT, theory, CSP, search, games |
| `crates/axiom-core/` | common contract, registry, Datalog adapter |
| `crates/axiom-ir/` | typed IR and S-expression serialisation |
| `crates/axiom-asp/` | ASP syntax, grounding, stable models |
| `crates/axiom-proof/` | trusted resolution kernel, STLC checker |
| `crates/axiom-prover/` | FOL parser, CNF, bounded resolution |
| `crates/axiom-planning/` | untyped STRIPS planner and validator |
| `crates/axiom-router/` | standard engine bundle |
| `crates/axiom-bridge/` | checked ASP-to-planning composition |
| `crates/axiom-bench/` | benchmark process driver |
| `benchmarks/external/` | differential oracle harness and workflow output |
| `tests/` | root integration, soundness, SAT, theory, V2 tests |
| `docs/v4/` | architecture, semantics, verification, benchmarks, limits |

## Performance posture

CPU-first, single-threaded, no GPU path, zero root dependencies. Existing
measurements (baseline `docs/v4/BASELINE.md`):

- first-argument index examines 495.8× fewer tuples than a scan;
- transitive-closure candidate growth ≈ 2.00 over `n = 100..800`, zero unbound
  scans;
- ~324 B RSS/fact with proofs, ~197 B without (501,500 facts);
- SAT corpus 9/9 with checked certificates.

The `rss kB` column in kernel output is sampled after the solver is dropped and
is **not** peak memory (`src/bench.rs:206-258`, F-03). Do not use it as a
baseline. A differential harness now exists (`benchmarks/external/` and the
`external differential benchmarks` workflow). Round 2 (run `39597261031`)
matched all 12 fixtures against Z3, clingo, Soufflé, Fast Downward, and Vampire,
with zero mismatches and zero skips. These are small correctness fixtures, not
a competitive performance claim.

## Documentation

| File | Contents |
|---|---|
| `docs/v4/ARCHITECTURE.md` | workspace layout, data flow, trust boundaries |
| `docs/v4/SEMANTICS.md` | exact fragment semantics and verdicts |
| `docs/v4/VERIFICATION.md` | evidence formats and what each verifier checks |
| `docs/v4/BENCHMARKS.md` | measured vs. counted, RSS defect, limits of claims |
| `docs/v4/KNOWN_LIMITATIONS.md` | what v4 cannot do and must not claim |
| `docs/v4/RELEASE_REPORT.md` | shipped changes and verification evidence |
| `docs/v4/CAPABILITY_MATRIX.md` | per-capability status |
| `docs/IR_SPEC.md` | root term/rule IR, stratification, serialisation |
| `docs/LANGUAGE_SPEC.md` | root surface syntax and errors |
| `docs/ALGORITHMS.md` | root algorithms and complexity boundaries |
| `docs/KNOWN_LIMITATIONS.md` | root engine limitations and retained defects |
| `docs/ROADMAP.md` | open work, including items v4 did not fix |

## Licence

MIT OR Apache-2.0.
