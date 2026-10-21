# Axiom v4 — branch analysis

Snapshot date: 2026-10-21. Counts are `git rev-list --left-right --count
main...origin/<branch>`: **behind main / unique to branch**. All branches were
inspected read-only; none was deleted or rewritten.

| Branch | Behind / unique | State | Contents relevant to v4 |
|---|---:|---|---|
| `main` | — | baseline `4c60f3f`, CI green | 29 modules, 153 tests, 4 benches, V2 capabilities |
| `base` | 34 / 0 | fully merged, historical | V1 frozen; no unique work |
| `v2` | 27 / 0 | merged (PR #1) | V2 representation set |
| `v2-play` | 22 / 0 | merged (PR #3) | full-game chess |
| `v2.5` | 9 / 0 | merged (PR #5) | V2 features + optimizations; tag `v2.5` |
| `v2.5-exp` | 17 / 0 | merged into `v2.5` | hyper-optimization experiments |
| `thorough-eval` | 8 / 3 | **open draft PR #6**, 10/10 CI green (run 37203710879) | +`tests/thorough_eval.rs` (478 lines) |
| `v3-slice-1` | 8 / 2 | **open draft PR #7**, 12/12 CI green (run 37623547988) | MCP server, TUI, `docs/V3.md`, workspace members |
| `ai-supervisor-system` | 8 / 1 | original branch of merged PR #8 | superseded by `736b6a1` and later fixes on `main` |
| `demo-parallel` | 21 / 1 | open draft PR #4 | not this project's work; ignore |
| `youtube-publish` | 3 / 0 | merged (PR #12) | CI-only publish pipeline |
| `youtube-verify-fix` | 1 / 0 | merged (PR #13) | verify best-effort |

## `thorough-eval` (PR #6)

Unique commits: `12f0fca` (suite), `aebfcaa` (self-play UCI replay fix),
`1faddc0` (Go setup fixes). The branch is 8 commits behind `main` and its only
file delta is `tests/thorough_eval.rs` (478 lines).

The suite is useful evidence: knowns, unknowns, malformed inputs,
determinism, and small benches. It is **not** part of the baseline test count
because it was never merged. It predates the theory module on `main`, so it
must be rebased and re-run before it can be trusted against v4.

**Recommendation.** After Stage 1's interface is fixed, port the suite onto
`v4` as an additional regression layer; do not merge the branch wholesale.
Treat its pass result as evidence about the older tree only.

## `v3-slice-1` (PR #7)

Unique commits: `e117187` (roadmap + `axiom-mcp` stdio server + TUI skeleton),
`f866803` (TUI double-borrow fix). Delta: 9 files, 1,094 insertions.

* `crates/axiom-mcp`: std-only stdio JSON-RPC server, 430 lines, depends only
  on the `axiom` path crate. Exposes `axiom_prove`, `axiom_sat`,
  `axiom_version`; 6 unit tests. The CI `mcp` job passes.
* `crates/axiom-tui`: 477 lines, 126 transitive crates (ratatui and an
  OpenAI/Anthropic client). The CI `tui` job passes.
* `Cargo.toml` gains `[workspace] members = ["crates/axiom-mcp",
  "crates/axiom-tui"]`.
* `docs/V3.md` is a roadmap, not an implementation record.

**Why it cannot be merged as-is into v4.** It is 8 commits behind `main`
(it predates the theory module and later fixes), it proposes a two-crate
workspace rather than the v4 interface, and the TUI drags a large dependency
tree into a project whose core is intentionally zero-dependency. The MCP server
is the valuable part.

**Recommendation.** Reuse the MCP design and tests as the basis of an
`axiom-mcp` crate *after* Stage 1/2 define the problem/evidence types. Keep the
TUI out of the core workspace or make it a separate, optional crate with its
own lockfile. Do not merge the branch to `main`.

## `ai-supervisor-system`

The original PR #8 branch. `main` already contains the merged supervisor
(`736b6a1`) plus four subsequent fixes for submit JSON, CLI parsing, package
name, and retry budgeting. The branch's one unique commit is superseded.

**Recommendation.** Archive; do not port. The standing project directive to
route repo work through the supervisor remains in force for ordinary tasks,
but the supervisor's `OPENCODE_API_KEY` was empty at last inspection
(2026-10-11). This v4 project is being executed directly because the task
requires sustained inspection across many files.

## Merged/irrelevant branches

`base`, `v2`, `v2-play`, `v2.5`, `v2.5-exp`, `youtube-publish`, and
`youtube-verify-fix` contain no unmerged work. `demo-parallel` is a
parallel-jobs demonstration that project memory says is not ours.

## Branch policy for v4

1. `v4` is the development branch, created from `4c60f3f`; `main` remains the
   known-good v2.5 baseline.
2. `v4-baseline` is an annotated tag on `4c60f3f` for recovery.
3. Stage checkpoints are commits on `v4`; a stage is not “done” until its
   targeted tests pass in CI.
4. Do not force-push, do not delete historical branches, and do not merge
   PR #6/#7 into `v4` without rebasing and re-running the full matrix.
5. If a v4 change must touch an existing module, preserve its public API or
   add a compatibility layer until the workspace migration is complete.

## Open PRs at audit time

| PR | Branch | Draft | State |
|---:|---|---|---|
| #4 | `demo-parallel` | yes | open (not ours) |
| #6 | `thorough-eval` | yes | open, green |
| #7 | `v3-slice-1` | yes | open, green |
