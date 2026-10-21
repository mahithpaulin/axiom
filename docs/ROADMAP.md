# ROADMAP

This is the current open-work list, not a history. Several items that older
versions of this file called “not implemented” now exist (SAT, CDCL(T), CSP,
search, ASP, FOL resolution, planning). The authoritative capability status is
`docs/v4/CAPABILITY_MATRIX.md`; the release evidence is
`docs/v4/RELEASE_REPORT.md`.

## 1. Correctness and trust

### 1.1 FOL equality

Ground equality is implemented by congruence closure over positive unit
equalities; other equality is encoded with reflexivity, symmetry, transitivity,
and congruence axioms. Both paths produce ordinary resolution proofs checked by
the same kernel.

Remaining work: superposition/paramodulation with kernel-checked steps, and
better control of the equality-axiom blow-up for non-theorems. Until then,
equality-heavy non-theorems may return `ResourceLimit` rather than `Unknown`.

### 1.2 Independent cross-checks

A manual differential harness now compares small fixtures against Z3, clingo,
Soufflé, Fast Downward, and Vampire. It is test-only; there is no runtime
dependency and no parity claim.

Remaining work: more FOL equality cases, more SMT-LIB cases, and larger
instances. Each new family must state skipped or unavailable oracles rather
than treating them as agreement.

### 1.3 Shared-code verification gaps

Datalog replay, ASP validation, and plan replay reuse the code under test.
Either build second implementations for the small checkers or state the trust
assumption prominently. The FOL kernel is the model: small, separately tested,
and fed serialised evidence.

### 1.4 SMT beyond difference logic

`crates/axiom-smt` reads a quantifier-free difference-logic subset of
SMT-LIB 2 and decides it over CDCL(T) with checked certificates.

`push`/`pop` scopes and several `check-sat` commands per file are supported,
but each check is solved from scratch: no learnt clause and no theory state is
reused, so the solving is not incremental yet.

Remaining work: general linear integer arithmetic (a Simplex or an
Farkas-based decision procedure), real incremental solving (assumption-based
clause reuse with theory lemmas scoped to their assumptions), a printer, and
an external conformance suite. Until then, a coefficient of `2` is
`Unsupported` rather than approximated.

### 1.5 B3 residual safety

The scheduling bug is fixed. Non-ground negation still blocks a derivation
rather than being rejected. Add a parse-time safety check or anti-join/tabling;
document whichever is chosen.

## 2. Measurement

### 2.1 Peak RSS

`src/bench.rs:206-258` samples after the solver drops. Switch to `peak_rss_kb`
(`VmHWM`) or sample inside the closure. Do not publish new memory claims until
this is fixed.

### 2.2 Dead benchmark code

`db_index_lookup` and `db_scan_lookup` call `.len()` on a slice; they measure a
pointer read, not candidate work. Consume the tuples through `black_box`.

### 2.3 Remove stub rows

`Bench::push` ignores its argument and callers append `Row::default_stub()`;
`report` prints a blank row per measurement. Delete the stub path.

### 2.4 v4 engine measurements

Add, with explicit caps:

- ASP enumeration scaling and grounding cost;
- FOL selected/generated clauses and proof size;
- planning states/expansions on small standard tasks;
- verifier time for each evidence format.

No external ranking; these are regression and boundary measurements.

## 3. Engine work

### 3.1 ASP

- a real grounder with joins/projection rather than full Cartesian assignment;
- aggregates and cardinality bounds, or an explicit permanent exclusion;
- conflict-driven learning (optional; correctness first);
- model-cap behavior made obvious in every consumer.

### 3.2 FOL

- equality (see 1.1);
- better clause selection and indexing;
- proof output in a standard format (TSTP/TPTP) if useful;
- a countermodel/finite-model path before ever emitting `Refuted`.

### 3.3 Planning

- typed PDDL, if the representation can stay honest;
- action costs and cost-aware A*/Dijkstra (an admissible unit-cost `h_max`
  heuristic is implemented);
- standard benchmark instances;
- keep `Impossible` restricted to exhaustive search.

### 3.4 Root theory engine

`rdl_chain_sat` allocates ~667 MB for 51 difference constraints. The driver
rebuilds too much state per assignment. Correctness is asserted; the cost is
the issue.

### 3.5 Root backward resolution

Close the known gaps in `docs/KNOWN_LIMITATIONS.md` B4–B6: ground-only goals,
positive-only bodies, depth 64, no negation. This requires tabling or an
explicit decision to leave backward mode as a narrow escape hatch.

## 4. Infrastructure

- CI the declared MSRV (`rust-version = "1.75"`) or raise it;
- a cross-engine conformance fixture format;
- a stable evidence schema with versioning, if evidence is ever exported;
- broader cross-domain composition only after a semantics-preserving
  translation exists (one checked ASP-to-planning pipeline is implemented).

## 5. Deliberately not planned

- competitive parity claims with specialist solvers;
- external solver dependencies at runtime;
- distributed/GPU execution;
- neural components;
- a universal formula IR that erases domain semantics;
- cross-domain “reasoning” that is only router dispatch relabelled.

## 6. Done criteria

An item is done when:

1. the implementation is in the default branch;
2. a test asserts the positive case and a negative/tamper case;
3. CI is green, including clippy and docs;
4. the capability matrix and limitations are updated in the same change;
5. any number quoted has a command and a run behind it.
