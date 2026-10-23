# Bounded AI optimization campaigns

`ai-optimize.yml` runs one bounded, inspectable improvement campaign against a
branch of this repository. It exists to turn the project's own quality
contracts into a closed loop: propose one small change, verify it with the same
commands CI runs, measure it, and keep it only when the evidence supports it.

The campaign never merges, never pushes to `v4` or `main`, and never edits
workflows, permissions, dependencies, or the target branch.

## Starting a campaign

1. Create a branch from `v4` whose name starts with `ai-optimization/`.
2. Push at least one commit to it.
3. Open a pull request from that branch into `v4`, or reopen an existing one.

The workflow checks out the pull request head branch, runs on `ubuntu-latest`,
and pushes checkpoint commits back to that same branch. Opening the pull request
is the only trigger; pushes made with `GITHUB_TOKEN` do not start another run.

The secret is only available to same-repository pull requests. Fork pull
requests are ignored by the job guard, and the guard also rejects any head
branch that does not start with `ai-optimization/`.

## What a run does

1. **Baseline.** Runs the workspace test command and two benchmark passes.
   Records test counts, wall time, RSS, and the exact head commit. If the
   baseline tests or benchmark cannot produce a usable result, the run stops:
   an unmeasurable baseline cannot support a claim.
2. **Model discovery.** Probes the free OpenCode models through
   `opencode models`. If none are reachable, the run continues with the
   deterministic tasks only and records the reason.
3. **Task selection.** Works through `targets/axiom-v4/backlog.json` in the
   pinned optimizer repository. The first five tasks are deterministic patches
   so the pipeline is exercised without a model; the rest are proposal-only
   model tasks.
4. **Proposal and application.** A model call runs in a temporary directory
   with **all tools disabled** and no repository credentials. It must return one
   JSON edit specification. Python applies exact `find`/`replace` edits and
   creates only paths inside the allowlist; the model never executes anything.
5. **Gates.** Every candidate must pass, in order:
   - `cargo fmt --all` then `cargo fmt --all -- --check`
   - `cargo clippy -p <package> --lib --tests -- -D warnings`
   - the task's targeted test command, when it adds one
   - the full workspace test command, with no drop in passing test count
   - for benchmark tasks, two benchmark runs compared with a two-run baseline
6. **Checkpoint.** Only a fully passing change is committed and pushed. Every
   attempt, including failures, writes a checkpoint, a redacted failure diff,
   model prompt/output, and logs under `ai-runs/<run-id>/`.
7. **Final report.** Re-runs the full suite and one benchmark, writes
   `FINAL_REPORT.md`, and uploads the whole run directory as an artifact. The
   report is also posted as a pull request comment.

## Editable surface

The model may only edit or create files under the prefixes in
`targets/axiom-v4/config.json`:

```
src/ crates/ tests/ benches/ examples/ docs/ benchmarks/
```

`.github/`, `.git/`, `.ai/`, `target/`, `ai-runs/`, `Cargo.toml`, `Cargo.lock`,
`rust-toolchain.toml`, `config/`, and `tools/security.py` are forbidden. The
driver re-checks the allowlist after formatting, so a formatter cannot silently
touch a protected file.

Additional hard rejections include added `#[ignore]`, removed `#[test]`,
process spawning, networking, `unsafe`, embedded credentials, `include_bytes!`,
`include_str!`, and any diff over the manifest's file, line, or byte limits.

## Benchmark policy

Wall-clock time on a shared runner is noisy. The gate uses the **best of two**
runs for both the baseline and the candidate, requires the best row to be at
least 2% faster, and rejects any row more than 15% slower.

RSS is recorded as a process-wide high-water mark (`VmHWM`). It is not a per-row
delta: after one large benchmark, every later row carries the same high-water
value. The report therefore shows wall time only and keeps RSS in `final.json`.
A memory claim needs a dedicated process and a dedicated probe; the current
kernel benchmark is a single process, so no backlog task is gated on RSS alone.

These thresholds are diagnostic, not a performance guarantee. The deterministic
counters in the bench log are the stronger signal.

## When the model is unavailable

Free-tier access can return `401`, `403`, or a rate limit. The driver treats
that as a finding, stops model calls, and records the reason. Deterministic
tasks still run. The report states plainly that the model was unavailable; it
does not fabricate proposals or retry around a quota.

## Reading a run

- `ai-runs/<run-id>/FINAL_REPORT.md` — summary, accepted commits, rejected
  attempts, benchmark table, final verification
- `ai-runs/<run-id>/state.json` — machine-readable campaign state
- `ai-runs/<run-id>/events.jsonl` — append-only event log
- `ai-runs/<run-id>/checkpoints/` — one checkpoint per attempt or soak
- `ai-runs/<run-id>/failures/` — redacted diffs and rejected specifications
- `ai-runs/<run-id>/model-calls/` — prompt and raw output per call
- `ai-runs/<run-id>/logs/` — cargo output for every gate

The branch itself contains the accepted commits. The pull request is the review
surface; no campaign result is merged automatically.

## Stopping a run

Close the pull request or cancel the workflow run. A cancelled job may leave the
last pushed checkpoint as the newest durable evidence. The branch is never
force-pushed, so earlier commits remain reviewable.

## Local use

The same driver can be run from a checkout of
`self-optimizing-opencode` against a clean Axiom checkout:

```bash
cd /path/to/self-optimizing-opencode
python3 -m tools.axiom_campaign \
  --target-dir /path/to/axiom \
  --run-id local-test \
  --branch ai-optimization/local-test \
  --minutes 30
```

The branch must already exist, must start with `ai-optimization/`, and must not
be `v4`. `--no-model` exercises the deterministic path without an API key.
