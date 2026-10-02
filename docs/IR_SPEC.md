# IR SPECIFICATION

The intermediate representation: what the exterior produces and the core
consumes. Normative for Stage 1.

---

## 1. Symbols

Every name is interned once and referenced by a `u32` thereafter. No `String`
appears on any path that the solver touches.

```
SymId  := u32
```

Three namespaces share one id space, distinguished by `SymKind`:

| Kind | Written | Notes |
|---|---|---|
| `SK_CONST` | `a` | arity 0, in argument position |
| `SK_FUN` | `f/1` | arity > 0, in argument position |
| `SK_PRED` | `p/2` | in atom position |

Namespacing matters: `a` as a constant and `a/0` as a nullary predicate are
**different symbols**. Identity is `(name, arity, kind)`.

**Case is significant.** `X` is a variable, `x` is a constant. The tokenizer
preserves case; lower-casing collapses every rule into a ground fact, which is a
soundness bug rather than a convenience.

---

## 2. Terms and atoms

```
TermId := u32
```

One node table, one child table, hash-consed:

```
TermNode { kind: u8, sym: SymId, start: u32, len: u16 }     -- 16 bytes
children: [TermId]                                          -- flat, shared
```

| `kind` | Meaning | `sym` | `children` |
|---|---|---|---|
| `T_VAR` | variable | variable id | empty |
| `T_CONST` | constant | `SK_CONST` symbol | empty |
| `T_FUN` | compound term | `SK_FUN` symbol | arguments |
| `T_ATOM` | predicate atom | `SK_PRED` symbol | arguments |

Atoms share the term space deliberately. A ground fact is then a single `u32`,
so deduplication is one integer comparison and the fact table is a
`HashSet<TermId>` rather than a set of vectors.

### 2.1 The hash-consing invariant

`intern(kind, sym, args)` returns the same `TermId` for the same triple, always.
This yields structural sharing, O(1) structural equality, cheap fingerprints,
and memoisation by integer.

### 2.2 The invariant hash-consing does *not* provide

**Unification merges distinct nodes** — `Var(3)` and `f(a)` become equivalent —
*outside* the hash-cons table. Two ids may therefore denote the same term after
a substitution is applied.

> **Rule.** Any code that compares terms for equality must resolve them first.

This is the sharpest edge in the design. `tests/soundness.rs` and the arena
invariant `TermStore::assert_no_dead_children` are what keep the fast path legal.

The child arena contains no dead storage: a duplicate `intern` returns the
existing node without appending, and the arena is gapless.

---

## 3. Variables and scope

Variables in a `Rule` are **rule-local slots** with ids unique across the whole
program. Two rules that both mention `X` get different variable ids, so their
atoms can never be confused.

`Rule.local_vars` lists exactly the variables that **occur** in the head or body,
in deterministic pre-order (head, then body literals left to right, arguments
left to right). A variable created by the builder but left unused is *not*
listed — otherwise the checker would demand an instantiation for it and reject
every derivation.

### 3.1 Fresh global variables

At solve time each rule is renamed once: local slots map to globally fresh
variables from `TermStore::fresh_var`. The renamed copy is cached and reused for
every firing, which is sound because each firing is fully undone at its trail
mark (DD-0009).

---

## 4. Literals and rules

```
Literal := { pos: bool, atom: TermId }
Rule    := {
    id:        RuleId,
    head:      T_ATOM,
    body:      [Literal],
    stratum:   u32,
    local_vars:[u32],
    backward_only: bool,
}
```

Stage 1 permits a single positive head only. Multiple heads, nested
disjunctions, and quantifiers are not in the representation.

### 4.1 `backward_only`

A rule whose head contains a function symbol defines an infinite relation, so
bottom-up evaluation cannot enumerate it. Such rules are marked `backward_only`
and:

* skipped by `saturate` / `saturate_naive`,
* usable by backward resolution,
* counted by `Program::forward_rules()` so callers can see what was skipped.

Reporting this explicitly is the point. The alternative — silently dropping the
rule, or storing non-ground facts — is worse in both directions.

---

## 5. Stratification

A predicate has a stratum. For a rule with head `h` and body literals over `p_i`:

```
positive literal:   stratum(h) >= stratum(p)
negative literal:   stratum(h) >  stratum(p)
```

Computed by bound relaxation (Bellman–Ford over `max`), which permits positive
cycles — transitive closure needs them — without a Tarjan pass. The result is
minimal and deterministic.

A negative edge that cannot be made strictly downward means **no stratification
exists**; the builder returns `ProgramError::NotStratified` rather than choosing
one. The exterior surfaces this as a parse error.

---

## 6. The database

```
Db := {
    seed:     HashSet<TermId>,   -- facts asserted in the program
    facts:    HashSet<TermId>,   -- seeds plus derivations
    by_pred:  [Vec<TermId>],     -- predicate -> tuples, insertion order
    by_first: [HashMap<TermId, Vec<TermId>>],   -- predicate -> first arg -> tuples
}
```

`seed` and `facts` are separate on purpose: `seed` is the only set a **strong**
proof check accepts without a derivation. A check that trusts the component it
is checking is not a check.

Insertion order is preserved and every iteration used for anything
order-sensitive is over a `Vec`, so the engine is deterministic despite using
hash maps internally. The closure fingerprint is an *additive* aggregate for the
same reason.

`by_first` is one index level; the trigger for adding a second is recorded in
DD-0006.

---

## 7. Substitutions

Not part of the IR proper, but the solvers' representation of assignment.

```
parent: [TermId]   -- union-find, self-parenting for roots
rank:   [u8]
trail:  [Trail]    -- Parent(child, old) | Rank(node, old)
```

* **Link direction is fixed** (DD-0004): a variable is always attached *under* a
  non-variable, so `resolve` always finds the concrete side.
* **No path compression** (DD-0005): every rewrite would need trailing for undo.
* The occurs check is mandatory and generation-stamped (DD-0003), and uses its
  **own** stack — sharing the unification stack destroys pending argument pairs.

### 7.1 `resolve`

Iterative post-order with an explicit frame stack, producing a hash-consed
result. A 100k-element list must not reach the native stack; `resolve` is
therefore iterative and so are all other traversals (`contains_var`, `walk`,
`first_bound`, term rendering).

---

## 8. Derivations

```
Derivation := {
    rule:   RuleId,
    concl:  TermId,             -- resolved, ground
    body:   [Literal],          -- ALL resolved premises, in rule body order
    inst:   [(u32, TermId)],    -- rule-local var id -> ground term
}

Proof := {
    goal:       TermId,
    root:       Option<DerivId>,
    steps:      [ResolutionStep],
    saturation: Option<Saturation>,
}

Saturation := { rounds: u32, idb_facts: u64, closure_hash: u64 }
```

Three properties are deliberate:

1. **Self-contained.** A derivation names a rule, an instantiation, and resolved
   premises. It holds no arena ids into mutable solver state, no back-pointers,
   and nothing about how it was found. A proof is therefore checkable by code
   that never ran the search.
2. **All premises recorded, in rule body order** — not in the order the join
   happened to visit them. The checker replays the inference exactly instead of
   trusting search order.
3. **`inst` keyed by rule-local var id**, not by arena node, so a record is
   stable under any internal renaming.

`closure_hash` is an additive (order-independent) fingerprint, so it cannot
depend on iteration order anywhere.

---

## 9. Programs

```
Program := {
    symbols:    SymbolTable,
    store:      TermStore,
    rules:      [Rule],
    num_strata: u32,
    pred_stratum: [u32],   -- indexed by SymId
    pred_idb:      [bool],
    pred_edb:      [bool],
    by_stratum:    [[RuleId]],
}
```

`pred_idb` includes predicates defined only by facts, because a fact is a rule
with an empty body. This has correct but non-obvious consequences; see DD-0017
before reading benchmark numbers that involve `idb_fact_count`.

---

## 10. Serialisation

**Not implemented.** No binary or textual IR dump exists in Stage 1. The
interchange format is the exterior's surface syntax plus the Rust builder API.
Recorded as a gap in `ROADMAP.md` rather than silently absent: a
"general-purpose engine" that cannot load a saved problem is not general-purpose,
and the hash-consed arena makes this harder than it looks — see the ROADMAP entry
for the design note.