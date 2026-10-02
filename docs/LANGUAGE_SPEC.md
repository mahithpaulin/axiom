# LANGUAGE SPECIFICATION

The surface syntax of the logical exterior. Normative for Stage 1.

Everything here is implemented in `src/exterior.rs` (553 lines) and documented in
`docs/IR_SPEC.md` for the representation it produces. Where this document and the
code disagree, the code wins; where they agree, this document is a description of
the code, not a design aspiration.

**The parser is compiled, not interpreted.** `exterior::parse` returns a
`Program`, not an AST that is walked later. Identifiers become interned `SymId`s,
terms become hash-consed 16-byte arena nodes, variables become rule-local slots,
predicates are stratified by bound relaxation, and rules whose heads contain a
function symbol are flagged `backward_only`. After `parse` returns, no part of
the engine can tell what the source text was; there is no `String` on any path
from the solver to a term comparison. The benchmark that watches for this is
`parse_program` (`benches/kernel.rs:490`).

---

## 1. Tokens

### 1.1 Accepted characters

The tokeniser (`src/exterior.rs:87`) is a single pass over `src.chars()`. There
is no escaping, no string literal, no quoting of any kind. The accepted set is:

| Class | Characters | Produces |
|---|---|---|
| newline | `\n` | nothing; `line += 1`, `col = 1` |
| whitespace | any `char::is_whitespace()` except `\n` | nothing |
| comment | `#` | nothing, to end of line |
| punctuation | `(` `)` `,` `.` | `LParen` `RParen` `Comma` `Dot` |
| arrow | `:` immediately followed by `-` | `ColonDash` |
| query arrow | `?` immediately followed by `-` | `QueryDash` |
| word | any `char::is_alphanumeric()`, plus `_`, `'`, `-` | `Ident(String)` or `Number(i64)` |

Everything else is an immediate error: `unexpected character 'c'`
(`src/exterior.rs:177`).

Consequences of that table, all of which are real behaviour:

* **No operators.** `-` is a word character, not a minus. `a-b` is one
  identifier; there is no subtraction. There is no `=`, `!=`, `+`, `*`, `/`,
  `;`, `|`, `[`, `]`, `{`, `}`, `<`, `>`, `&`, `!`, `@`, `^`, `~`, `"`, `` ` ``.
  Each of those produces `unexpected character`. In particular `p/2` is not
  writable in the source language; arity comes from the number of arguments.
* **`is_alphanumeric` is Unicode-aware, `is_variable` is not.** `Ärger` is a
  legal identifier and, because `is_variable` tests `is_ascii_uppercase`
  (`src/exterior.rs:402`), it is a **constant**. Only ASCII `A`–`Z` starts a
  variable.
* **Identifiers may contain apostrophes and hyphens.** `X'`, `a-b`, `_`,
  `succ'` are all single tokens.

### 1.2 Comments

`#` starts a comment that runs to the next `\n` (`src/exterior.rs:108-112`). The
newline itself is then processed normally, so a comment does not need a trailing
newline and there is no block-comment syntax. A `#` inside an identifier is not a
comment: identifiers are scanned as whole words and `#` is not a word character,
so `p(a) # x` is `p(a)` followed by a comment.

### 1.3 Words: integers versus identifiers

A word is lexed as an integer only if the **entire** word parses as `i64`
(`src/exterior.rs:180`):

```
007        -> Number(7)          leading zeros are discarded
-5         -> Number(-5)         the hyphen is a word character, so this is one word
1a         -> Ident("1a")        a constant named "1a", not a number
9223372036854775808 -> Ident(...) an out-of-range literal silently becomes a constant
```

Integer tokens are accepted **only in argument position** (inside `f(...)`).
A predicate name is read with `ident()` (`src/exterior.rs:250`), which requires
`Tok::Ident`, so `?- 1(a).` fails with `expected an identifier`. Integers carry
no arithmetic: `n(1).` and `n(2).` are two facts and nothing relates them. There
are no arithmetic constraints anywhere in Stage 1 (see `KNOWN_LIMITATIONS.md`).

### 1.4 Case

**Case is preserved and is semantically load-bearing.** `src/exterior.rs:187-190`:

> Case is *preserved*. Lowercasing collapses `X` into the constant `x`, silently
> turning every rule into a ground fact — a soundness bug, not a style choice.

`exterior::uppercase_is_a_variable` (`src/exterior.rs:493`) pins this: `q(X).`
must fail with `a fact must be ground`, not succeed as a ground fact. Commit
`0f2df13 fix: preserve identifier case` exists because this was once wrong.

There is no normalisation of any kind: no trimming of apostrophes, no
canonicalisation of number spellings beyond the `i64` round trip, no case folding
anywhere in the crate.

### 1.5 Token limit

`limits.max_tokens` bounds the length of `out: Vec<Spanned>`. After every
iteration of the scan loop, `if out.len() > limits.max_tokens` fails with
`token limit exceeded` (`src/exterior.rs:194-196`). The default is
`1 << 22` = 4 194 304 tokens.

What this actually protects: `Spanned` is `{ tok: Tok, line: u32, col: u32 }`,
and `Tok::Ident` owns a `String`, so each token costs roughly 40 bytes of struct
plus its own text. The default ceiling therefore authorises on the order of
200 MB of token vector before a single parse action runs. That is the memory
attack the limit bounds; the tokeniser is otherwise linear in `src.len()`.

Note that the token limit is enforced *before* any grammar rule, so a program
that is both too long and malformed reports `token limit exceeded` first.

---

## 2. Grammar

Written in the exact shape `Parser::item` / `body` / `atom` / `term`
(`src/exterior.rs:261-396`) accepts. `ε` means empty.

```
program ::= item*

item    ::= query | rule | fact

query   ::= '?-' atom '.'
rule    ::= atom ':-' body '.'
fact    ::= atom '.'

body    ::= lit ( ',' lit )*            -- at least one lit
lit     ::= [ 'not' | 'neg' ] atom

atom    ::= ident
          | ident '(' ')'                        -- nullary, arity 0
          | ident '(' term ( ',' term )* ')'

term    ::= number                       -- integer constant
          | ident                        -- variable or constant, see §3
          | ident '(' term (',' term)* ')'  -- compound, at least one argument
```

Whitespace between any two tokens is optional and insignificant.

### 2.1 Facts

`p(a, b).` A fact must be **ground** and must be an atom. Both are checked at
`src/exterior.rs:387-392`:

```text
q(X).            -> error: a fact must be ground
p(f(X)).         -> error: a fact must be ground
```

A fact is stored as a rule with an empty body (`Builder::fact`,
`src/program.rs:282`), which is why a fact-only predicate is still marked IDB
(DD-0017).

### 2.2 Rules

`head :- lit_1, lit_2, ... .`

* The head must be an atom; there are no compound-term heads in the surface
  language.
* A body must contain at least one literal. `p :- .` fails because `.` is not
  the start of an atom (`expected an identifier`); see §6 on the dead
  `a rule needs at least one body literal` check.
* Variables are rule-local. Two rules mentioning `X` get distinct variable slots
  (`Builder::var`, `src/program.rs:226`), so their atoms can never be confused.
* The trailing `.` is mandatory: `edge(a,b) :- edge(a,b)` is an error
  (`expected '.' after rule`). Commit `1e99066` and `0f2df13` both touched this.
* Rules are stratified at build time by bound relaxation (`src/program.rs:396`).
  Positive edges require `stratum(h) >= stratum(p)`; negative edges require
  `>`.

### 2.3 Negation

`not` and `neg` are interchangeable and are the *only* negation forms. They are
not reserved words: `not.` parses as a nullary fact with the predicate `not`,
because the keyword is only recognised in body position by an exact token-text
comparison (`src/exterior.rs:340-349`). `Not` and `NOT` are not negation; they
are predicate names, so `safe(X) :- node(X), Not blocked(X).` is a three-literal
body.

This is **stratified negation**, not negation-as-failure. `not q(X)` means "the
atom `q(X)` is absent from the least model", it does not mean "the engine failed
to prove `q(X)`". Negation-as-failure is refused by design (DD-0002).

### 2.4 Queries

`?- atom .`

A query is a single atom followed by `.`. Not a term, not a conjunction, not
disjunctive, no trailing semicolon. Queries are **not** part of the `Program`:
`parse` collects them into `Parsed::queries` as bare `TermId`s
(`src/exterior.rs:201-205`, `363-369`) and they are never evaluated by `parse`
itself. `exterior::parse` does not run anything; the caller passes
`parsed.queries[i]` to `Solver::prove` or `Solver::query`.

A program consisting only of queries has `rules.len() == 0` and
`queries.len() == n`. An empty program is **valid** and yields zero rules and
zero queries (`src/exterior.rs:516`; `tests/robustness.rs:114`).

### 2.5 Compound terms and integers

Compound terms nest arbitrarily and appear in argument position only:

```text
p(f(g(a, b), h(1, -2))).
```

* A compound term needs **at least one** argument: `f()` in term position is
  `a compound term needs at least one argument` (`src/exterior.rs:291`).
* A **nullary atom `p()` is accepted** and is the arity-0 predicate `p/0`
  (`src/exterior.rs:321`). The asymmetry with `f()` is deliberate in the code:
  atoms go through `Builder::atom(name, 0, &[])` and terms go through
  `Builder::func`.
* Integers become constants interned under their decimal rendering
  (`src/exterior.rs:269-272`), so `1` and `01` are the same constant while `1`
  the number and `1` the identifier are the same token anyway. There is no
  arithmetic, no comparison, and no typing.
* Term symbols and predicate symbols share one id space but are namespaced by
  `SymKind` (`src/symbol.rs:21-23`), so the constant `a` and the nullary
  predicate `a` are different symbols.

### 2.6 Complete example

```text
# a small graph and its transitive closure
edge(a, b).
edge(b, c).
edge(c, d).
blocked(c).

node(a).
node(b).
node(c).
node(d).

path(X, Y) :- edge(X, Y).
path(X, Z) :- path(X, Y), edge(Y, Z).
safe(X)    :- node(X), not blocked(X).

?- path(a, d).
?- safe(X).
```

Compiling and running it:

```rust
let parsed = axiom::exterior::parse(src).unwrap();   // 11 facts + 3 rules
let goal = parsed.queries[0];

let mut s = axiom::Solver::new(parsed.program);
let mut b = axiom::Budget::steps(1_000_000);
let out = s.prove(goal, &mut b);
assert_eq!(out.status, axiom::Status::Proved);
assert!(s.verify(out.proof.unwrap()).is_ok());
```

`safe/1` lives in a strictly higher stratum than `blocked/1`
(`stratified_negation_5000`, `benches/kernel.rs:351`).

---

## 3. Variables

`is_variable` (`src/exterior.rs:399-405`) is exactly:

```rust
match name.chars().next() {
    Some(c) if c.is_ascii_uppercase() || c == '_' => true,
    _ => false,
}
```

So a name is a variable if and only if its **first** character is an ASCII
uppercase letter or an underscore.

| Written | Kind |
|---|---|
| `X`, `Y0`, `Z'` | variable |
| `_`, `_anon`, `_0` | variable |
| `x`, `a`, `succ`, `n1` | constant |
| `Ärger` | constant (not ASCII uppercase) |

Consequences:

* Variables are recognised **only in term (argument) position.** A predicate
  name goes through `ident()`, which accepts only `Tok::Ident` and does not
  consult `is_variable`. So `X(a).` is `expected an identifier`, and `?- X.`
  likewise.
* `_` is an ordinary named variable, not an anonymous one. `p(X, _) :- q(X, _).`
  binds the *same* variable twice, because `Builder::var` keys on the name
  string. This is intentional and used in the test corpus
  (`p(X) :- e(X,_).`, `tests/determinism.rs:91`).
* A variable in a fact is rejected (`a fact must be ground`). A variable in a
  query is fine.
* Variables in a rule become rule-local slots, and only variables that actually
  *occur* in the head or body are listed in `Rule::local_vars`
  (`src/program.rs:318`, `340`). An unused builder variable must not be listed,
  or the proof checker would demand an instantiation for it and reject every
  derivation.
* At solve time each rule is renamed once to globally fresh variables and the
  copy is cached (`Solver::ensure_renamed`, `src/solver.rs:162`). Reuse is sound
  only because every firing is fully undone at its trail mark (DD-0009).

---

## 4. Limits

```rust
pub struct Limits {
    pub max_tokens: usize,   // default 1 << 22 = 4_194_304
    pub max_depth:  usize,   // default 256
    pub max_arity:  usize,   // default 4096
    pub max_rules:  usize,   // default 1 << 20 = 1_048_576
}
```

`parse` uses `Limits::default()`; `parse_with` takes a `Limits` by value, so a
caller raises or lowers an axis with a struct literal:

```rust
use axiom::exterior::{parse_with, Limits};

let tiny = Limits { max_depth: 3, ..Default::default() };
assert!(parse_with("p(a(a(a(a(a))))).", tiny).is_err());
```

| Field | Default | Enforced at | What it protects against |
|---|---|---|---|
| `max_tokens` | `1 << 22` | `tokenize`, after each scanned token (`src/exterior.rs:194`) | Unbounded allocation in the token vector, and the total size of any program. Each token carries its own `String` for `Ident`, so this is the axis that bounds memory. |
| `max_depth` | `256` | `term` and `atom`, `if depth > max_depth` (`src/exterior.rs:262`, `310`) | Native-stack exhaustion. `term`/`atom` are the only recursive-descent routine in the crate; everything else (`walk`, `resolve`, `contains_var`, `rename`) is iterative precisely so that term depth cannot reach the stack. |
| `max_arity` | `4096` | `term` and `atom`, `if args.len() > max_arity` (`src/exterior.rs:282`, `324`) | The per-literal argument `Vec` and the hash-consed child block for one node. Note the check is `> max_arity`, so exactly `max_arity` arguments are legal. |
| `max_rules` | `1 << 20` | `Parser::item`, `if self.rules > limits.max_rules` (`src/exterior.rs:373`) | The `rules` vector, the per-rule `renamed` cache, and the cost of the stratification relaxation, which is `O(rounds * rules)` with `rounds <= num_preds + 2` (`src/program.rs:396-418`). |

Two limits do **not** count what you might expect:

* `max_rules` counts only `:-` items. Facts and queries are bounded solely by
  `max_tokens`, and each fact becomes a `Rule` *and* a `Db` entry, so the
  practical fact ceiling under the defaults is on the order of 10^6.
* Nothing limits the number of distinct identifiers, so the `SymbolTable` grows
  with the token count rather than with `max_rules`.

### 4.1 Two internal bounds that a raised `Limits` can violate

Both defaults sit comfortably below a fixed internal representation bound, so
neither is reachable under `Limits::default()`. Both are reachable the moment a
caller raises a limit, and both fail **silently** rather than loudly:

| Raised past | Silent consequence |
|---|---|
| `max_arity > 65_535` | `TermNode.len` is a `u16` (`src/term.rs:51`), and `intern` stores `len: args.len() as u16` (`src/term.rs:229`). An arity of 65 536 stores `len = 0`; the atom loses all its arguments. |
| `max_depth > 4096` | `TermStore::rename` hard-codes `const MAX: usize = 4096` and returns the subterm **un-renamed** when depth exceeds it (`src/term.rs:288-292`). A rule with deeply nested arguments then gets a renamed copy whose inner variables were never freshened. |

`tests/robustness.rs:218-225` already parses a 200 000-deep term with
`max_depth: 500_000`. It does not currently expose the `rename` bug because that
program contains no rules, so `ensure_renamed` never runs — but the combination
is a live hazard for any caller who follows that pattern. Treat 4096 as a hard
ceiling on `max_depth` until `rename` grows a real depth guard.

---

## 5. Limits are errors, never hangs

§21 of the charter requires the exterior to treat input as hostile. The parser
meets that in the strong form: every failure is a `ParseError` carrying a
position, nothing panics, and nothing loops. `ParseError` is
`{ line: u32, col: u32, message: String }` and displays as
`{line}:{col}: {message}` (`src/exterior.rs:60-64`). `tests/robustness.rs`
feeds it empty input, unbalanced brackets, `"\0\1\2"`, an emoji, a 100 000-character
identifier, and a 200 000-deep term, and requires only that each call *returns*.

Tokeniser errors report the position of the offending character. Parser errors
report the position of the current token, or of the last token in the stream if
the failure is at end of input (`src/exterior.rs:217-227`).

`tokenize` is `pub`, but `Spanned`'s fields are private to the module, so from
outside the crate the token stream is not inspectable — only its length and its
error are.

---

## 6. Every error message

Exact strings. `self.err(...)` in `src/exterior.rs`, plus the `ProgramError`
`Display` impl in `src/program.rs:84-106` which `parse_with` re-wraps as a
`ParseError` at line 0, column 0 (`src/exterior.rs:425-429`).

### 6.1 Tokeniser

| Message | Cause |
|---|---|
| `unexpected character 'c'` | character outside the accepted set of §1.1 |
| `token limit exceeded` | more than `limits.max_tokens` tokens |

### 6.2 Parser

| Message | Cause |
|---|---|
| `expected an identifier` | predicate name position, where a `Number` or a non-identifier token appeared (`ident()`, `src/exterior.rs:256`; also reachable for `X(a).`, `?- X.`, `p(a) :- .`) |
| `expected a term` | argument position with neither a `Number` nor an `Ident` (`term()`, `src/exterior.rs:303`) |
| `nesting depth limit exceeded` | `depth > limits.max_depth`, checked in both `term` (`src/exterior.rs:262`) and `atom` (`src/exterior.rs:310`) |
| `arity limit exceeded` | more than `limits.max_arity` arguments in one literal, in `term` (`src/exterior.rs:282`) or `atom` (`src/exterior.rs:324`) |
| `a compound term needs at least one argument` | `f()` in term position (`src/exterior.rs:291`) |
| `expected ')'` | closing parenthesis missing; raised by `expect(&Tok::RParen, "')'")` at `src/exterior.rs:290` or `332` |
| `a fact must be ground` | a variable occurs in a fact (`src/exterior.rs:390`) |
| `expected '.' after query` | `?-` goal not followed by `.` (`src/exterior.rs:367`) |
| `expected '.' after rule` | rule not followed by `.` (`src/exterior.rs:384`) |
| `expected '.' or ':-'` | a bare atom followed by something that is neither `:-` nor `.` (`src/exterior.rs:386`) |
| `rule limit exceeded` | more than `limits.max_rules` rules (`src/exterior.rs:373`) |
| `a rule needs at least one body literal` | **unreachable**: `body()` always parses at least one literal before returning (`src/exterior.rs:337-361`). The check at `src/exterior.rs:377` is defensive. |
| `rule head must be an atom` | **unreachable**: `atom()` always returns a `T_ATOM` node (`src/program.rs:236-247`), so the `kind(head) != T_ATOM` test at `src/exterior.rs:380` cannot fail. |
| `a fact must be an atom` | **unreachable**, for the same reason (`src/exterior.rs:387`). |

### 6.3 Builder, surfaced through the parser

| Message | Cause |
|---|---|
| `program is not stratified: negative cycle through predicate #{pred}` | a negated edge that cannot be made strictly downward, so no least model exists (`src/program.rs:87-91`). Reported at `0:0` because it is a whole-program property, not a local syntax error. `tests/robustness.rs::unstratified_negation_is_rejected` requires the message to contain `stratified`. |
| `predicate #{pred} declared with arity {declared} but used with arity {used}` | `ProgramError::ArityMismatch` (`src/program.rs:92-100`). **Unreachable from the exterior**: a predicate is interned per `(name, arity)`, so `p(a).` and `p(a,b).` are two different predicates and no mismatch can arise. `arity_check` exists for programs built through the Rust `Builder` API. |
| `invalid predicate declaration '{name}'` | `ProgramError::BadPredicate` (`src/program.rs:101-103`). **Unreachable from the exterior**: `Builder::atom` handles the empty name by interning a private unnamed symbol (`src/program.rs:237-243`) instead of erroring. |

A positive cycle is **not** an error: `p :- q. q :- p.` parses fine
(`tests/soundness.rs::stratification_rejects_negative_cycles`), because positive
cycles are exactly what transitive closure needs.

---

## 7. `show`: rendering a `Program` back to source

`exterior::show` (`src/exterior.rs:438`) prints rules only. Facts print as
`head.`; rules print as `head :-\n  lit,\n  lit.` with negated literals prefixed
`not `. It does **not** print queries — they are not in the `Program`.

Variable names are not preserved: `TermStore::show` renders a variable as `_`
followed by its slot id (`src/term.rs:326-329`). That still re-parses correctly,
because variables are rule-local and `is_variable` accepts a leading `_`.
`exterior::show_round_trips` (`src/exterior.rs:540`) asserts that the re-parsed
text yields the same rule count.

This is a debug and proof-rendering facility, not a serialisation format. There
is no IR dump of any kind in Stage 1 — see `docs/IR_SPEC.md` §10 and
`docs/KNOWN_LIMITATIONS.md`.

---

## 8. What the language cannot express

Named so their absence is unambiguous. Full treatment in `docs/KNOWN_LIMITATIONS.md`.

* Disjunction, in heads or bodies. One positive head, per `Rule`
  (`src/program.rs:61-71`).
* Quantifiers, or any explicit variable binding.
* Negation in the head, or negation-as-failure.
* Unstratified negation. It is rejected, not approximated.
* Arithmetic, comparisons, or any arithmetic theory.
* Strings, characters, lists in `[...]` form, arrays, records.
* Aggregates, recursion control (`cut`, `!`), exceptions.
* Modules, includes, or any way to compose two source files. One program is one
  `parse` call.
* Mode declarations or type declarations. Arity is inferred from use; there is
  nothing to declare and nothing to check.
* Anything the exterior cannot encode as a stratified Horn rule. That includes
  CDCL clauses, constraints, plans and games — those are roadmap items
  (`docs/ROADMAP.md`), not syntax.