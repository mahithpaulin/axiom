# Axiom v4 — release report

Status: release candidate on branch `v4`.
Code verification run: `39591302192` at `77ca7ac`
(2026-10-21). Documentation-only and capability-string edits after that commit
are covered by the final CI run recorded in the PR.

## 1. What this release adds

Axiom v4 turns the repository into a workspace with one common engine contract:

- `axiom-core`: `Problem`, `Verdict`, `Evidence`, `Engine`, `EngineRegistry`,
  routing records, and the Datalog adapter;
- `axiom-ir`: typed structural IR and deterministic S-expression
  serialisation;
- `axiom-asp`: finite ASP grounding, stable-model enumeration, and independent
  model validation;
- `axiom-proof`: a small trusted resolution kernel and an STLC type checker;
- `axiom-prover`: FOL parsing, NNF/Skolem/CNF, bounded given-clause resolution,
  and a verified prover engine;
- `axiom-planning`: untyped STRIPS PDDL, grounding, BFS planning, and plan
  replay;
- `axiom-router`: the standard four-engine bundle with verification on every
  definite outcome.

Existing root capabilities (Datalog, SAT, CDCL(T), CSP, search, games) remain
available and keep their own tests and certificates.

## 2. Verification evidence

Run `39591302192` (all 10 jobs successful):

| Job | Result |
|---|---|
| `test` | 231 passed, 0 failed, 0 ignored across 17 targets |
| `doc` | 6 doc tests passed |
| `clippy` | clean with `-D warnings` over the workspace, lib + tests |
| `fmt` | clean |
| `known-defects` | no ignored tests remain |
| `examples` | all examples build |
| `bench-ci`, `bench-sat`, `bench-theory`, `diag` | successful; no new perf claim |

The run includes the B3 regression, all kernel negative tests, ASP truncation
and non-model tests, the FOL smuggled-input test, the planning tampered-plan
test, and the router domain sweep.

## 3. Correctness changes

- **B3 fixed**: forward evaluation no longer checks negation immediately after a
  delta seed. Negation is evaluated after all positive joins, so a later
  positive literal can bind the negated variable. Regression:
  `negation_waits_for_later_positive_bindings`.
- **Proof rule serialisation** now matches the five-field `resolve` form.
- **ASP positive loop** test corrected: `p :- p.` has the empty set as its only
  stable model; the engine already implemented that and the test was wrong.
- **Planning and prover** compile/clippy/test defects found by CI were fixed
  before this report.

## 4. What is deliberately not claimed

- No competitive performance claim against clingo, Vampire, Fast Downward, Z3,
  Soufflé, or Lean.
- No complete first-order theorem prover. The prover is bounded, has no
  equality, and never emits `Refuted`.
- No formal verification. The kernel is a small checker, not a proved
  metatheory.
- No complete ASP count when the model cap is reached.
- No “impossible” planning answer from a resource cap.
- No cross-domain composition beyond routing.
- No valid peak-RSS numbers from the kernel benchmark column.

## 5. Fragment summary

| Domain | Decides | Main caps | Negative result |
|---|---|---|---|
| Datalog | least model, ground goals, queries | root step/depth budgets | `Refuted` only from completed least model |
| ASP | stable models over finite Herbrand universe | 22 atoms, 200k ground rules, 1024 models | `Impossible` only when complete and zero |
| FOL | refutations by bounded resolution | 4096 clauses, 2048 selected, 8192 generated | never `Refuted`; saturation is `Unknown` |
| Planning | shortest untyped STRIPS plan | 100k actions, 50k states, 100k expansions | `Impossible` only after exhaustive BFS |
| STLC | type inference/checking | structural | typing error |

## 6. Upgrade and compatibility notes

- The root crate remains zero-dependency and keeps its public API.
- v4 crates are workspace members with path dependencies; they are not
  published.
- `Cargo.lock` is still gitignored.
- Root docs that previously denied SMT, theory, planning, and search were stale;
  they are corrected in this release.
- The RSS column in kernel output is still post-solve; it is documented as
  invalid for peak memory, not silently reinterpreted.

## 7. Open work

- external differential suites and a conformance harness;
- in-closure peak-RSS measurement;
- ASP performance and a real grounder;
- FOL equality and countermodel/`Refuted` support (or an explicit decision to
  omit them permanently);
- planning heuristics and cost-aware search;
- cross-domain evidence translation;
- MSRV CI for the declared 1.75;
- root theory allocation blow-up (`rdl_chain_sat`).

Nothing in this report should be read as a promise that those are complete.
