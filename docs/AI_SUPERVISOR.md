# AI Supervisor — autonomous coding tasks from Termux

Submit a task from your phone, put the phone away, and let GitHub Actions do
the work. Queue = GitHub issues labelled `ai-task`. Workers = bounded
`ai-supervisor.yml` runs. State = the issue (hidden JSON block + status
labels + comments). No phone, Codespace, or Kaggle session needs to stay on.

```text
Termux                        GitHub                          Actions runner
  |                              |                                   |
  |-- agentctl submit "do X" --->|                                   |
  |   (creates issue, exits)     |-- issues/opened event ----------->|
  |                              |   validate (NO secrets):          |
  |                              |   trusted author? bounds ok?      |-- execute (has OPENCODE_API_KEY):
  |                              |   mark running, set branch        |   branch ai-task/N-slug
  |                              |                                   |   loop <=3: opencode run -> cargo test
  |                              |<-- checkpoint comments + push ---|   -> commit + push + comment
  |                              |                                   |   final label: completed /
  |-- agentctl status N -------->|   needs_review / failed           |   needs_review / failed / cancelled
```

## Setup (in order)

1. **Labels + CLI** (from a repo checkout in Termux):
   ```bash
   ln -sf "$PWD/tools/agentctl" ~/bin/agentctl
   agentctl setup
   ```
   `setup` creates the `ai-task` and `ai-status-*` labels and checks auth.
2. **Secret**: add `OPENCODE_API_KEY` at
   `https://github.com/<owner>/<repo>/settings/secrets/actions`.
   Value = your OpenCode Zen API key from `https://opencode.ai/auth`
   (generate it in a browser; never paste it in chat or commit it).
   The existing `OPENCODE_API_KEY` secret (used by the `/oc` workflow) is
   reused — no second credential needed.
3. **Merge this to the default branch.** `issues` / `issue_comment` triggers
   only fire from the workflow file on the default branch (`main`).
4. **Verify**: `agentctl submit "Create file ai-task-smoke-test.txt containing exactly: smoke ok"` —
   then `agentctl status <N>` and `agentctl logs <N>`.

## Usage

```bash
agentctl submit "Implement feature X, add tests, and fix any failures"
agentctl submit "Fix the clippy warnings in src/solver_fwd.rs" --model opencode/space-bunny-free --max-iters 2
agentctl status 42        # status, branch, commit, latest supervisor note
agentctl list             # all ai-task issues with statuses
agentctl logs 42          # durable issue record + recent runner log tail
agentctl retry 42         # posts /retry (attempt budget enforced server-side)
agentctl cancel 42        # posts /cancel; a running worker stops at checkpoint
```

Statuses: `queued` → `running` → `completed` | `needs_review` | `failed` |
`cancelled`. Failed / `needs_review` tasks accept `/retry` while attempts
remain (default budget: 1 run + 1 retry).

## Security

- **Untrusted authors can never reach the secret.** The `validate` job runs
  with no secrets and only lets `OWNER`/`MEMBER`/`COLLABORATOR` issues start
  the worker. Stranger issues are ignored without comment (no spam oracle).
- **Least privilege.** Top-level workflow permissions are empty. `validate`
  gets `issues: write` only; `execute` gets `contents` + `issues` +
  `pull-requests` + `actions` (artifact upload) — no admin, no org, no deploys.
- **Bounded.** Defaults: 3 iterations/attempt, 2 attempts/task, 55 min job
  cap, per-call timeouts, 200 KB log cap. No polling loops, no self-dispatch,
  no budget self-expansion (the task text is treated as untrusted data and the
  worker prompt forbids following embedded budget/permission instructions).
- **Hygiene.** The controller refuses to commit `.env`, `*.pem`, `*token*.json`,
  `auth.json`, Kaggle files, etc. `GITHUB_TOKEN` is never exported into the
  model's environment; issue updates run from the shell. Nothing merges to
  `main` automatically — open a PR from the task branch when ready.
- **Model.** Default `opencode/space-bunny-free` (zero-retention, free for a
  limited time). Whatever `--model` you pass is used verbatim — a paid Zen
  model bills your Zen credits, so check
  https://opencode.ai/docs/zen/#pricing first. Free models change over time;
  if the default stops working, resubmit with a current `-free` model.

## Recovery

- **Interrupted worker** (timeout, runner death, cancelled run): the last
  pushed checkpoint survives on `ai-task/<N>-<slug>`. Status stays `running`
  until you act: comment `/retry` (or `agentctl retry N`) to resume from the
  existing branch — the controller checks out and pulls it, never recreating
  or duplicating commits. Stale `running` after a dead run is normal; a retry
  or cancel clears it.
- **Duplicate events** (re-delivery, relabel): `decide` ignores events when
  status is `running`/final/`cancelled`, and the concurrency group serialises
  runs per issue. No duplicate branches or commits.
- **Retry says budget exhausted**: attempts reached `max_attempts`. Either fix
  up the branch yourself or resubmit as a new task.
- **Logs expired**: runner logs and artifacts (7-day retention) expire; the
  issue comments + commits are the durable record and never expire.
- **No branch yet**: the worker hasn't started (wait ~1 min) or validation
  rejected the task (see issue comments / `agentctl status`).

## Troubleshooting

| Symptom | Likely cause | Fix |
|---|---|---|
| Issue stays `queued`, no run | Workflow not on `main`, or secret missing | Merge PR; add `OPENCODE_API_KEY` |
| `failed`, "OPENCODE_API_KEY secret is not configured" | Secret absent | Add the secret, `/retry` |
| `needs_review` with commits | Tests still red after budget | Review branch, fix, PR — or `/retry` |
| `failed`, no commits | Model produced nothing usable | Narrow the task, resubmit |
| `retry` refused: not retryable | Status is `completed`/`cancelled`/`running` | New task, or `--force` for completed |
| Run starts for a stranger's issue | Impossible by design — report it | Check `validate` job log |
| opencode errors about the model | Free model rotated/renamed | Resubmit with a current `-free` model from `opencode models` |

## Cost / limits

- **GitHub Actions**: free and unlimited on public repos like this one; the
  55 min job cap and iteration bounds keep each task small anyway.
- **Zen models**: `-free` models cost nothing but are rate-limited and
  rotated; paid models bill per-token credits with auto-reload possible —
  set a monthly limit at opencode.ai if you ever use one.
- **Codespaces / Kaggle**: not used by the supervisor. Heavy GPU work still
  goes through the existing Kaggle loop when a task genuinely needs it.

## Files

- `tools/agentctl` — the Termux CLI (bash + `gh` only).
- `tools/agentctl-config.example.sh` — env knobs, placeholders only.
- `.github/workflows/ai-supervisor.yml` — validate + execute worker.
- `.github/scripts/ai_supervisor.py` — parsing/state/decision logic.
- `.github/scripts/test_ai_supervisor.py` — 33 unit tests (`python3 test_ai_supervisor.py`).
- `.github/scripts/ai-controller.sh` — bounded iteration loop run inside CI.
