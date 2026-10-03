# axiom — symbolic reasoning engine

A general symbolic reasoning engine in Rust. One intermediate representation,
several solvers, machine-checkable proofs. Zero runtime dependencies.

```text
EXTERNAL WORLD  ──▶  LOGICAL EXTERIOR  ──▶  LOGICAL IR  ──▶  LOGICAL CORE  ──▶  Status + Proof
                   (only place with        (Program)      (no domain
                    domain knowledge)                       knowledge)
```

```rust
use axiom::{exterior, Budget, Solver, Status};

let src = "\
edge(a, b).
edge(b, c).
path(X, Y) :- edge(X, Y).
path(X, Z) :- path(X, Y), edge(Y, Z).
?- path(a, c).
";
// The exterior compiles source into the IR. The core sees no domain concepts.
let parsed = exterior::parse(src).unwrap();
let goal = parsed.queries[0];
let mut solver = Solver::new(parsed.program);

let mut budget = Budget::steps(1_000_000);
assert_eq!(solver.least_model(&mut budget).unwrap().idb_facts, 5);

let out = solver.prove(goal, &mut budget);
assert_eq!(out.status, Status::Proved);
let proof = out.proof.expect("a definite status carries a proof");
assert!(solver.verify(&proof).is_ok());   // re-derived from the rules alone
```

## Status — read this before trusting anything

This is **Stage 1**. It implements **stratified Datalog**: facts, rules with
positive and stratified-negated bodies, function symbols in rule heads handled by
resolution rather than saturation, and complete least-model computation.

**The test suite is green with no exclusions.** Two completeness defects that
used to be `#[ignore]`d (ROADMAP I5, I6) were fixed in `src/solver_fwd.rs`:
after each derived solution the join undid the substitution to the rule-entry
mark, discarding the seed bindings, so every second and later solution per
seed ran with unbound variables — heads came out non-ground and were dropped.
Undoing to the join's resume point instead keeps the seed. The differential
test and the `non_ground_heads` canary that caught it stay in the suite as
regression coverage.

No CDCL/SAT, no SMT, no constraint propagators, no symbolic arithmetic, no
search, no strategy selection, no neural components, no IR serialisation. See
`docs/KNOWN_LIMITATIONS.md`, which is itemised and deliberately unflattering.

## The honesty contract

> A status that claims knowledge carries a proof object. A status that does not
> (`Exhausted`, `Unknown`) carries none, and must never be read as a negative
> answer.

`Refuted` specifically means *absent from the least model, and the least model
was computed to completion* — never "the search gave up". It is only reachable
when backward resolution exhaustively returns `NotProvable`; any decline (depth
bound, negated body, non-ground subgoal) reports `Unknown` with the reason.

General first-order validity is undecidable, so no complete procedure exists.
The engine reports that rather than hiding it.

## Verification

`Solver::verify` re-derives a goal from program facts and rules **without using
the solver's substitution, arena, or join**. That duplication is deliberate: a
checker sharing the solver's unification cannot catch a unification bug.

`tests/reference.rs` is a second, independent implementation — string terms, naive
fixpoint, no index — used for differential testing. It shares no code with the
engine, so agreement is evidence rather than tautology.

```
cargo test                              # 80 pass, 2 ignored with reasons
cargo test -- --ignored                 # run the known-defect tests
cargo bench --bench kernel              # full suite
cargo bench --bench kernel -- quick     # fast subset
cargo bench --bench kernel -- diag      # scaling probe with work counters
```

## Documentation

| File | Contents |
|---|---|
| `docs/ARCHITECTURE.md` | Layers, data flow, the status contract, the generality test |
| `docs/IR_SPEC.md` | Terms, atoms, rules, stratification, derivations — normative |
| `docs/LANGUAGE_SPEC.md` | Surface syntax, limits, every error message |
| `docs/ALGORITHMS.md` | What is implemented, what it costs, where it stops being correct |
| `docs/DESIGN_DECISIONS.md` | 17 decisions, each with hypothesis → alternatives → measurement. Reversals kept |
| `docs/KNOWN_LIMITATIONS.md` | What this cannot do, and why |
| `docs/ROADMAP.md` | Ordered next steps and eight numbered open defects |

## Performance posture

CPU-first, single-threaded, no GPU path. 16 bytes per term node; a term is a
`u32`; duplicate interning allocates nothing (asserted, not claimed). Measured:
a first-argument index examines **495.8× fewer tuples** than a scan (the second
level measures the same on argument 1); transitive-closure join cost fits slope
**2.00** over n ∈ {100, 200, 400, 800} with zero unbound scans (was 3.0 with
256M unbound at n=800), 0.41 s for 321,200 facts.

Memory is the price: ~324 bytes of RSS per derived fact against ~20 B of IR
payload with proofs on — the second index level cost ~76 B/fact for a 95×
speedup — and ~197 B/fact with `ProofMode::Off`, which reports `Found` rather
than `Proved` because it records nothing to check.

## Licence

MIT OR Apache-2.0.