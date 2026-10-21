# Axiom v4 — verification

Verification means: given the original problem and a claimed outcome, a checker
reconstructs enough to accept or reject it. It does not mean the search is
correct, and it is not formal verification of the implementation.

## 1. Contract

`axiom_core::Engine` requires:

```rust
fn verify(&self, problem: &Problem, outcome: &Outcome) -> Result<(), VerifyError>;
```

Rules enforced across engines:

- A definite verdict (`Proved`, `Refuted`, `Found`, `Impossible`) must carry
  evidence.
- An inconclusive verdict (`Unknown`, `Unsupported`, `ResourceLimit`, `Error`)
  must not carry evidence; the FOL and planning verifiers reject evidence on
  inconclusive outcomes explicitly.
- Evidence has a `kind` and a textual `payload`.
- Verification re-runs from the problem; it does not accept the solver's
  in-memory state.
- `Router::solve` calls `verify` on every definite outcome and turns a failure
  into `RouterError::Verification`.

## 2. Evidence kinds

| Kind | Engine | Definite verdicts | Payload |
|---|---|---|---|
| `axiom-datalog-closure` | Datalog | `Found` | rounds, IDB fact count, closure hash |
| `axiom-datalog-goal` | Datalog | `Proved`, `Refuted` | verdict and ground goal |
| `axiom-datalog-query` | Datalog | `Proved`, `Refuted` | verdict, answer count, saturation hash |
| `axiom-asp-models` | ASP | `Found`, `Impossible` | complete flag, count, counters, universe, models |
| `axiom-fol-resolution` | FOL | `Proved` | S-expression resolution proof |
| `axiom-plan` | Planning | `Found` | length, search counters, action sequence |
| `axiom-plan-exhausted` | Planning | `Impossible` | state/action counters |

Evidence payloads are intentionally simple text. None is a stable public
serialisation format yet.

## 3. Per-engine checks

### 3.1 Datalog adapter

`crates/axiom-core/src/datalog.rs`

1. Parse the problem again and create a fresh solver.
2. Solve with a 100,000,000-step verification budget.
3. Require the fresh verdict and evidence to equal the claimed ones.
4. For a ground goal, re-run `prove` and check the returned derivation with
   `Solver::verify`.
5. For a non-ground goal, re-run `query` and verify every answer's derivation.

Limitations: this is a repeat execution of the same parser and solver, not a
second implementation. A shared bug would reproduce the same wrong answer.
Closure evidence is checked by recomputing the closure, not by an independent
proof of every fact.

### 3.2 ASP

`crates/axiom-asp/src/lib.rs`

1. Re-parse and re-ground the program.
2. Require the universe size to match the evidence.
3. Validate each listed model with `stable::validate_model`, which recomputes
   the reduct and least closure.
4. Re-enumerate with the same model cap and require the serialised evidence to
   match exactly.
5. If the claimed enumeration was complete, require the model count to match
   the fresh enumeration.

A truncated (`complete=false`) result is still evidence-checked for the models
listed, but it is not a complete count. `Impossible` requires a complete
enumeration with zero models.

Limitations: search and validation share `is_stable`. A bug in that predicate
would affect both. Negative tests cover non-models, positive loops, constraints,
and truncation, but there is no second stable-model implementation.

### 3.3 FOL prover

`crates/axiom-prover/src/lib.rs`

1. Re-parse the problem.
2. Recompute the deterministic CNF of `axioms ∧ ¬goal`.
3. Parse the S-expression proof.
4. Require every `Input` clause in the proof to appear in the reconstructed
   CNF. This blocks a valid-looking refutation that smuggles in an axiom.
5. Run `axiom_proof::check_resolution`, which:
   - rejects forward references and out-of-range literal indices;
   - re-runs unification with an occurs check;
   - reconstructs each resolvent and factoring step and compares it with the
     recorded clause;
   - requires the final clause to be empty.

The kernel trusts the input clauses but not the prover's resolution steps. The
CNF converter is inside the prover's trust boundary; it is tested on small
formulas but not formally verified. `Proved` is emitted only after the kernel
accepts the proof.

Negative tests include a tampered clause, smuggled empty input, malformed
evidence, and non-theorems (`Unknown`, not `Refuted`).

### 3.4 Planning

`crates/axiom-planning/src/lib.rs`

Found plan:

1. Re-parse the PDDL task.
2. Parse the action sequence.
3. Require its length to match the evidence.
4. Replay from the initial state, checking applicability and effects.
5. Require the goal at the end.

Impossible:

1. Re-parse the task.
2. Re-run exhaustive search (A* with `h_max`) with a 10,000,000-step
   verification budget and the same caps.
3. Accept only `PlanStatus::Impossible`; a found plan is a mismatch and a cap
   is a verification resource limit.

A tampered plan test moves the item in the wrong direction and is rejected.

Limitations: replay and search share the transition implementation. `Impossible`
is only as good as the grounding, heuristic, and cap accounting. The heuristic is
admissible: it ignores negative preconditions and delete effects, so it can only
underestimate the true remaining cost.

### 3.5 Bridge

`crates/axiom-bridge/src/lib.rs`

`BridgeOutcome::verify` recomputes the entire pipeline from the request, requires
the same selected model index, injected/ignored atom sets, and translated
`PlanningTask`, and requires identical planning verdict and evidence. The
planning stage itself replays the plan against the translated task. Tests cover a
successful injection, an ignored undeclared predicate, an arity mismatch, a
missing model, and a changed-request verification failure.

Limitations: both stages share their own engines' verification code; the bridge
does not independently prove that the ASP model or PDDL translation is correct.

### 3.6 Router

`crates/axiom-router/src/lib.rs`

The router selects by declared kind and delegates verification to the producing
engine. It adds no verification logic of its own. Tests cover one problem per
domain, no-engine routing, and malformed input remaining an error.

## 4. Trust assumptions

| Assumption | Status |
|---|---|
| Rust compiler and standard library are correct | Trusted |
| `axiom-proof` kernel is small and reviewed | Trusted base; tests only |
| CNF/Skolem conversion preserves satisfiability | Trusted prover-side code; tested, not proved |
| ASP stable-model predicate is correct | Trusted implementation; tests only |
| Datalog parser/solver is correct | Trusted implementation; independent replay only |
| PDDL parser and transition relation are correct | Trusted implementation; replay shares code |
| Evidence parsers reject malformed input | Tested per engine |
| Budget accounting cannot be bypassed | Code inspection and tests; no formal proof |

The project does **not** claim formal verification, proof of the kernel in a
proof assistant, or conformance to an external standard.

## 5. Negative tests that must stay

These are part of the acceptance criteria:

- `tests/soundness.rs::negation_waits_for_later_positive_bindings` — B3.
- `crates/axiom-proof` `a_tampered_clause_is_rejected`,
  `occurs_check_prevents_cycles`.
- `crates/axiom-prover` `tampered_evidence_is_rejected`,
  `smuggled_input_is_rejected`, `a_non_theorem_is_unknown_not_refuted`,
  `equality_substitution_is_proved_and_verified`,
  `non_ground_equality_falls_back_to_axioms_and_proves`,
  `unsupported_arithmetic_is_explicit`.
- `crates/axiom-asp` `validator_rejects_a_non_model`,
  `truncation_is_not_reported_as_complete`,
  `unsat_constraint_is_impossible_only_after_complete_enumeration`,
  `positive_loop_does_not_support_its_head`.
- `crates/axiom-planning` `tampered_plan_is_rejected`,
  `proves_impossibility_by_exhaustion`, `typed_input_is_unsupported`,
  `astar_and_bfs_return_shortest_plans`,
  `astar_respects_negative_preconditions`.
- `crates/axiom-bridge` `stable_model_supplies_planning_init`,
  `undeclared_predicates_are_ignored`, `arity_mismatch_is_rejected`,
  `missing_model_is_rejected`, `verification_detects_a_changed_request`.
- `crates/axiom-router` `unknown_kind_is_an_explicit_route_error`,
  `malformed_input_is_not_a_found_verdict`.

## 6. What is not verified

- The external differential harness is a small functional cross-check, not a
  conformance proof. It reports missing oracles as skipped and cannot establish
  agreement when an oracle is absent.
- No proof of the CNF transformation, grounding, stable-model test, or plan
  transition relation.
- No proof that the step budget is enforced on every allocation path.
- No proof-carrying certificate for `Impossible`; it is a re-run.
- No complete model count when the ASP model cap is reached.
- No `Refuted` for FOL, because there is no countermodel builder.
- No verification of the root SAT/theory/CSP/game engines in this document;
  those have their own checkers and tests described in the older docs.

## 7. Reproducing

```sh
cargo test --workspace --lib --tests
cargo test --workspace --doc
cargo clippy --workspace --lib --tests -- -D warnings
cargo fmt --all -- --check
```

GitHub Actions is the authoritative environment. Local Android/Termux runs are
a developer convenience and can execute the same commands, including release
builds, but are not a CI substitute. See `docs/v4/BENCHMARKS.md` for the CI jobs
and `docs/v4/RELEASE_REPORT.md` for the release runs.
