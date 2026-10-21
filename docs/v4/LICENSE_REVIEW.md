# Axiom v4 — licence review

Reviewed: 2026-10-21. This is an engineering record, not legal advice.

## 1. Axiom's own licensing status

| Item | Finding |
|---|---|
| `Cargo.toml` | `license = "MIT OR Apache-2.0"` |
| `README.md` | “Licence: MIT OR Apache-2.0” |
| `LICENSE`, `LICENSE-MIT`, `LICENSE-APACHE`, `COPYING` | **absent** |
| GitHub licence detection | `null` (no licence file) |
| `src/` file headers | no SPDX identifiers |

Under default copyright, the absence of a licence file means the repository is
**all rights reserved**, even though the manifest and README express an intent
to dual-license. The intent is not operative for third parties until the
licence texts are present.

**Recommended action (owner decision).** Add the standard MIT and Apache-2.0
texts, keep the existing dual-licence intent, and add a short note to
`README.md` explaining which files (if any) are excluded. This is a
publication/legal decision, so it is recorded rather than performed during
Stage 0. It is not a blocker for internal v4 development.

## 2. Reference projects

Licences were read from the repositories on 2026-10-21. GitHub's licence
detector mislabels Z3 as “Other”; its `LICENSE.txt` is the MIT text, which is
what matters.

| Project | Licence | Copyleft? | Obligations if code were reused | v4 policy |
|---|---|---|---|---|
| Z3 (`Z3Prover/z3`) | MIT | No | Include copyright + permission notice in copies/substantial portions | Reference only; no code reuse |
| Soufflé (`souffle-lang/souffle`) | UPL-1.0 | No | Include the UPL notice; permissive, with patent language | Reference only; no code reuse |
| clingo (`potassco/clingo`) | MIT | No | Include copyright + permission notice | Reference only; no code reuse |
| Vampire (`vprover/vampire`) | Modified BSD-3-Clause | No | Retain notice; no endorsement; honour the modification clause | Reference only; no code reuse |
| Lean 4 (`leanprover/lean4`) | Apache-2.0 | No | Include licence + NOTICE; patent grant/termination terms | Reference only; no code reuse |
| Fast Downward (`aibasel/downward`) | GPL-3.0 | **Yes** | Linking/deriving would force the combined work under GPL-3.0 | **Behavioral reference only; no source reuse** |

### Important distinction

Algorithmic ideas, published papers, input/output formats, and observable
behavior are not the same as source code. Axiom v4 will study the reference
implementations and published descriptions, then write independent Rust. This
is the standard clean-room posture and is compatible with all six licences.

What v4 will **not** do:

* copy source files, comments, identifier names, or data structures verbatim
  from any reference project;
* vendor a reference implementation into the build;
* link a GPL-3.0 component into the MIT/Apache core;
* present a wrapper around an external binary as an Axiom implementation.

## 3. Per-engine reuse rules

| Engine | Reference | Rule |
|---|---|---|
| SMT | Z3 | Implement the supported fragment from the SMT-LIB semantics and standard DPLL(T)/Nelson–Oppen literature. Z3 may be used as a test-only oracle, not a runtime dependency. |
| Datalog | Soufflé | Reimplement semi-naive evaluation, indexing, and provenance from the published algorithm. No source reuse. |
| ASP | clingo | Reimplement the scoped ASP subset and stable-model semantics. No source reuse. |
| FOL prover | Vampire | Reimplement resolution/factoring and later superposition from the calculus literature. No source reuse. |
| Proof kernel | Lean 4 | Reimplement a small independent kernel from the calculus definition. No source reuse, no Lean runtime dependency. |
| Planning | Fast Downward | **Clean-room only.** GPL-3.0 forbids copying source into Axiom's permissive core. Use papers, documentation, and black-box behavior. |

## 4. Test oracles and differential testing

External solvers may be run in CI or locally as **oracles**:

* they must not be shipped or required at runtime;
* their outputs must be parsed into Axiom's own evidence types and re-checked
  by Axiom's verifier;
* a missing oracle must cause a test to be skipped with an explicit reason,
  never a silent pass;
* oracle versions must be pinned and recorded with the benchmark result;
* oracle licences must permit this use (all six do for testing; Fast Downward
  remains unmodified and unlinked).

This matches the project's existing DD-0007 stance: external solvers in tests,
never in the shipped reasoning path.

## 5. Data and benchmark licensing

* Prefer Axiom-generated datasets with a recorded seed and a generator script.
* If a public benchmark corpus is vendored, record its licence and attribution
  next to the data. A solver's licence does not automatically cover its test
  data.
* The existing frozen SAT corpus in `benches/data/` is small and generated
  in-project; no external corpus is currently vendored.

## 6. Dependency policy for the v4 workspace

1. **Core crates** (`axiom-core`, `axiom-ir`, `axiom-sat`, `axiom-datalog`,
   `axiom-smt`, `axiom-asp`, `axiom-prover`, `axiom-proof`, `axiom-planning`,
   `axiom-search`, `axiom-router`) should remain dependency-free where
   practical. Any dependency must be permissively licensed (MIT, Apache-2.0,
   BSD, ISC, UPL) and recorded with a reason.
2. **Optional frontends/tools** (MCP, TUI, benchmark harness) may use crates,
   but must not force them on the core. A separate lockfile or feature flag is
   acceptable.
3. **Forbidden in the core:** GPL/AGPL/SSPL code, proprietary SDKs, paid
   services, network calls at solve time.
4. **Serde/JSON:** if serialisation is added, prefer a small, well-audited
   crate or a hand-written encoder for the stable IR; the choice is a Stage 2
   decision, not an assumption.
5. **Lockfiles:** commit `Cargo.lock` for the workspace once dependencies
   exist, so CI and release builds are reproducible.

## 7. Attribution

If any code, data, or generated artefact is later derived from a reference
project, add a `THIRD_PARTY_NOTICES` file with the project, version, licence,
and the files affected. At present no such derivation exists.

## 8. Open actions

| # | Action | Owner | Blocking? |
|---|---|---|---|
| L1 | Add `LICENSE-MIT` and `LICENSE-APACHE` matching the declared dual licence | repo owner | No, but required before a public v4 release |
| L2 | Decide whether v4 remains MIT/Apache-2.0 or changes | repo owner | No for development; yes for release |
| L3 | Audit the unmerged `v3-slice-1` TUI dependency licences before any reuse | v4 implementer | No |
| L4 | Keep Fast Downward strictly clean-room | v4 implementer | Yes for Stage 9 |
| L5 | Record oracle versions in benchmark output | v4 implementer | No, before external comparisons |
