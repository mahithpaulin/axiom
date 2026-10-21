# Axiom v4 — semantics

This document defines the meaning of each v4 fragment. Where an input falls
outside a fragment, the required result is `Unsupported` or `Error`; it is never
silently reinterpreted.

## 1. Common conventions

- Signatures are finite and untyped unless a fragment says otherwise.
- Symbol names are case-sensitive.
- There are no implicit axioms, no built-in arithmetic, and no equality unless
  a fragment explicitly imports it.
- Every search is bounded by a deterministic step budget and, where stated, a
  structural cap.
- A definite verdict requires evidence. Inconclusive verdicts carry no
  evidence and are not negative results.

## 2. Datalog (root `axiom` crate)

### 2.1 Fragment

Facts and rules with positive or stratified-negated body literals. The program
must be stratified: no cycle through a negated dependency. The parser rejects
negative cycles. Terms are finite first-order terms; function symbols in rule
heads make a rule `backward_only` and are not saturated forward.

The engine computes the least model of the program. A ground goal is
`Proved` when a derivation exists in that model and `Refuted` when the goal is
absent from the completed least model. A non-ground goal is answered by query
enumeration; each answer carries a derivation.

### 2.2 Negation

Negation is stratified negation, not default negation. For a candidate
substitution, a negated literal succeeds only when it is fully ground and the
ground atom is absent from the database.

Programs are expected to be *safe*: every variable in a negated literal should
be bound by a positive literal in the same rule. The forward engine does not
reject every unsafe program. A negated literal that never becomes ground blocks
that derivation. This is sound with respect to the intended safe fragment but
incomplete outside it; an unsafe program can therefore omit facts that a
different semantics might derive.

B3 (fixed in `4726ca0`) was a scheduling bug: negation was tested immediately
after a delta seed, before later positive literals had bound its variables. The
regression `negation_waits_for_later_positive_bindings` requires
`p(X,Y) :- q(X), not r(Y), s(Y).` to derive both `p(a,b)` and `p(b,b)`.
Negation is now tested only after all positive joins complete.

### 2.3 Status mapping

| Root `Status` | v4 `Verdict` | Meaning |
|---|---|---|
| `Proved` | `Proved` | Derivation exists and is checked |
| `Refuted` | `Refuted` | Completed least model lacks the ground goal |
| `Found` | `Found` | Model/query answer found |
| `Impossible` | `Impossible` | Reserved by the root API; not produced by Datalog |
| `Unknown` | `Unknown` | Search declined; no negative claim |
| `Exhausted` | `ResourceLimit` | Budget or depth stopped work |

A closure request with no goal returns `Found` with a closure certificate.

## 3. Answer-set programming (`axiom-asp`)

### 3.1 Syntax

Supported statements:

```text
fact.                         p(a).
normal rule.                  q(X) :- p(X), not r(X).
choice rule.                  { s(X); t(X) } :- p(X).
integrity constraint.         :- p(X), not q(X).
show directive.               #show s/1.
```

Terms are variables or constants; there are no function symbols. Aggregates,
cardinality bounds, optimisation, `#external`, `#include`, and `#minimize` are
rejected.

### 3.2 Grounding

The Herbrand universe is the finite set of constants appearing in the program.
Every safe variable is instantiated over that universe; the resulting ground
rules form the ground program. Safety requires every variable in a rule to
appear in a positive body literal (or in the head of a choice rule as allowed by
the implementation). Unsafe programs return `Unsupported`.

Caps: at most 22 atoms in the ground universe and 200,000 ground rules.
Exceeding either is `ResourceLimit`, not a partial answer.

### 3.3 Stable models

For a candidate set `X` of ground atoms:

1. Facts must be in `X`; they seed the reduct.
2. A choice rule whose body is true in `X` may seed any selected head atom.
   Choice heads are not automatically true.
3. Normal rules whose negative body is false in `X` (i.e. every negated atom is
   absent from `X`) are retained.
4. The least closure of the retained positive rule bodies, starting from the
   seeds, is computed.
5. `X` is stable iff the closure equals `X` and no integrity constraint body is
   true in `X`.

A positive loop such as `p :- p.` has the empty set as its only stable model;
the loop does not justify `p`. `p. :- p.` has no stable model.

### 3.4 Enumeration and verdicts

Enumeration checks every candidate subset in deterministic mask order. With
`max_models = 0` the cap is 1024; with a positive value it is that value.

- Zero models with a complete enumeration: `Impossible`.
- At least one model: `Found`.
- Cap reached before enumeration ends: `Found` with `complete=false`; the
  evidence lists only the models found and must not be read as a complete count.
- Universe/rule/budget cap: `ResourceLimit`.

Every listed model is independently validated by the stable-model test.
Completeness is claimed only when `complete=true`.

## 4. First-order logic (`axiom-prover`)

### 4.1 Syntax

```text
axiom <formula>.
goal <formula>.
pred p/1.
fun f/1.
const a.
```

Formulas support `true`, `false`, `not`/`~`/`!`, `and`/`&`, `or`/`|`, `->`,
`<->`, `forall x, y. ...`, and `exists x. ...`. Predicate and function arities
are fixed by declaration or first use. Variables are exactly those bound by a
quantifier; an unbound identifier used as a term is a constant.

No equality, sorts, arithmetic, higher-order constructs, or type declarations.
`a = b` is rejected as unsupported rather than interpreted.

### 4.2 Calculus

1. Negate the goal and take the union with the axioms.
2. Eliminate `<->`, push negation inward to NNF, rename bound variables to
   avoid capture.
3. Skolemise existentials with deterministic fresh function symbols/constants.
4. Distribute to CNF; clauses are normalised by sorting and deduplicating
   literals.
5. Run given-clause resolution with factoring under caps:
   `max_clauses = 4096`, `max_selected = 2048`, `max_generated = 8192`, plus
   the caller's step budget.
6. On the empty clause, serialise the resolution proof and check it with the
   trusted kernel.

A refutation is a proof that the negated goal plus axioms are unsatisfiable,
hence the goal follows. `Proved` is emitted only after the kernel check passes.

### 4.3 Verdicts

- `Proved`: kernel-checked refutation exists.
- `Unknown`: the search saturated without finding the empty clause. This does
  **not** mean the goal is invalid; validity is undecidable and the search is
  bounded.
- `ResourceLimit`: a clause, selection, generation, or step cap stopped work.
- `Unsupported`: equality, arithmetic, sorts, or another excluded construct.
- `Error`: malformed input or an internal inconsistency.
- `Refuted`: never emitted. There is no model/countermodel construction.

## 5. STRIPS planning (`axiom-planning`)

### 5.1 Fragment

Untyped STRIPS PDDL with:

- `:predicates`, domain `:constants`, problem `:objects`;
- actions with `:parameters`, conjunctive `:precondition`, and conjunctive
  add/delete `:effect`;
- negative preconditions;
- conjunctive goals;
- `:strips` and `:negative-preconditions` requirements.

Typing, equality, numeric fluents, conditional effects, quantified or
disjunctive goals, action costs, and durative actions are rejected as
`Unsupported`.

### 5.2 Transition semantics

A ground action is applicable in state `S` iff all positive preconditions are in
`S` and all negative preconditions are absent. Applying it produces
`(S \ deletes) ∪ adds`. The initial state is the set of ground `:init` atoms.
A goal is satisfied iff every goal literal holds in the final state.

Grounding uses action parameters over objects and constants. At most 100,000
ground actions are allowed; beyond that is `ResourceLimit`.

### 5.3 Search and verdicts

The engine uses A* with the admissible delete-relaxation `h_max` heuristic by
default; `planner::plan` selects breadth-first order for compatibility. Both
orders enumerate states in nondecreasing plan length (unit action cost) and
return a shortest plan. Caps: 50,000 stored states and 100,000 expansions.

- `Found`: a plan reaches the goal. Verification replays the exact action
  sequence.
- `Impossible`: search exhausted the reachable state space without a plan.
  Verification re-runs the exhaustive search.
- `ResourceLimit`: a cap or the step budget stopped the search. This is not
  impossibility.

## 6. Simply typed lambda calculus (`axiom-proof::stlc`)

The kernel also contains a small STLC type checker: types are base types,
arrows, and products; expressions are variables, abstractions, applications,
pairs, projections, and typed constants. `infer_type` returns a type or a
`KernelError::Stlc`; `check_type` compares the inferred type with an expected
one. This checks typing, not logical consistency, termination, or the correctness
of a compiler.

## 7. Router semantics

`Router::standard()` dispatches by `ProblemKind` in a fixed order. It does not
merge semantics. A precise answer from the router is exactly the answer of the
selected engine plus a successful call to that engine's verifier. Routing
failures and verification failures are errors.

The router does not translate evidence itself. One separate pipeline,
`axiom-bridge`, composes ASP and planning:

1. enumerate and verify the ASP outcome, then decode the selected stable model;
2. drop atoms whose predicate is not declared by the PDDL domain, and reject a
   shared predicate with the wrong arity or an unknown object;
3. add the remaining atoms to the task's initial state;
4. solve the translated task and replay the plan against it.

`Found` therefore means a plan exists for the combined initial state. It does
not assert anything about the planning task without the ASP facts, nor that the
selected stable model is unique. Other cross-domain compositions, including
Datalog-to-theory and ASP-to-SMT filtering, are not implemented.

## 8. Resource-limit semantics

A `ResourceLimit` is a statement about the run, not about the problem. It
carries no evidence and must not be cached as a final answer. The same input
with a larger budget may return a definite verdict; the reverse is not licensed.

Wall-clock budgets are best-effort and platform-dependent. Deterministic step
counters are the reproducibility mechanism.
