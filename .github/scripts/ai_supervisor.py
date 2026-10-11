#!/usr/bin/env python3
"""Helpers for the ai-supervisor worker and the agentctl CLI.

Stdlib only. All parsing / state-transition logic lives here so it can be
unit-tested (see test_ai_supervisor.py) instead of hiding inside workflow YAML.

Durable task state is stored as a hidden JSON block inside the GitHub issue
body:

    <!-- ai-task: {"task_id": "...", "status": "queued", ...} -->

Status labels on the issue mirror the status: ``ai-status-queued``,
``ai-status-running``, ``ai-status-needs_review``, ``ai-status-completed``,
``ai-status-failed``, ``ai-status-cancelled``.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import sys

TASK_LABEL = "ai-task"
STATUS_PREFIX = "ai-status-"
CANCELLED_LABEL = STATUS_PREFIX + "cancelled"

STATUSES = (
    "queued",
    "running",
    "retryable",
    "needs_review",
    "completed",
    "failed",
    "cancelled",
)
FINAL_STATUSES = ("completed", "failed", "cancelled")
RETRYABLE_STATUSES = ("failed", "needs_review")

# Authors with these associations may submit tasks. Anything else (including
# NONE for unknown users) is untrusted and must never trigger a worker that
# holds the OPENCODE_API_KEY secret.
TRUSTED_ASSOCIATIONS = ("OWNER", "MEMBER", "COLLABORATOR")

BLOCK_START = "<!-- ai-task:"
BLOCK_END = "-->"

DEFAULT_MODEL = "opencode/space-bunny-free"
DEFAULT_MAX_ITERATIONS = 3
DEFAULT_MAX_ATTEMPTS = 2  # 1 initial run + 1 retry
MAX_ITERATIONS_LIMIT = 5
MAX_ATTEMPTS_LIMIT = 3


def slugify(text: str, max_len: int = 40) -> str:
    """Turn free-form text into a safe git-branch slug."""
    slug = re.sub(r"[^a-z0-9]+", "-", text.lower()).strip("-")
    slug = re.sub(r"-{2,}", "-", slug)
    return (slug or "task")[:max_len].strip("-") or "task"


def branch_name(issue_number: int, slug: str) -> str:
    return f"ai-task/{issue_number}-{slugify(slug)}"


def parse_task_body(body: str) -> dict:
    """Extract the hidden ai-task JSON block from an issue body."""
    if not body or BLOCK_START not in body:
        return {}
    try:
        raw = body.split(BLOCK_START, 1)[1].split(BLOCK_END, 1)[0]
        data = json.loads(raw.strip())
        return data if isinstance(data, dict) else {}
    except (json.JSONDecodeError, IndexError):
        return {}


def render_task_block(data: dict) -> str:
    return f"{BLOCK_START}{json.dumps(data, sort_keys=True)}{BLOCK_END}"


def upsert_task_block(body: str, updates: dict) -> str:
    """Return body with the hidden state block merged with updates."""
    data = parse_task_body(body or "")
    data.update(updates)
    block = render_task_block(data)
    if BLOCK_START in (body or ""):
        pre, _, rest = body.partition(BLOCK_START)
        _, _, post = rest.partition(BLOCK_END)
        return f"{pre}{block}{post}"
    return f"{block}\n\n{body or ''}"


def status_from_labels(labels: list[str]) -> str:
    """Read the current status from ai-status-* labels. Defaults to queued."""
    for label in labels:
        if label.startswith(STATUS_PREFIX):
            status = label[len(STATUS_PREFIX):]
            if status in STATUSES:
                return status
    return "queued"


def is_trusted(association: str) -> bool:
    return (association or "").upper() in TRUSTED_ASSOCIATIONS


def validate_task(data: dict, repo: str) -> list[str]:
    """Check task fields. Returns a list of human-readable errors (empty=ok)."""
    errors = []
    if not (data.get("task") or "").strip():
        errors.append("task description is empty")
    target = data.get("repo", "")
    if target and target != repo:
        errors.append(f"target repo {target!r} does not match supervisor repo {repo!r}")
    try:
        mi = int(data.get("max_iterations", DEFAULT_MAX_ITERATIONS))
    except (TypeError, ValueError):
        errors.append("max_iterations is not an integer")
    else:
        if not 1 <= mi <= MAX_ITERATIONS_LIMIT:
            errors.append(
                f"max_iterations {mi} out of bounds (1..{MAX_ITERATIONS_LIMIT})"
            )
    try:
        ma = int(data.get("max_attempts", DEFAULT_MAX_ATTEMPTS))
    except (TypeError, ValueError):
        errors.append("max_attempts is not an integer")
    else:
        if not 1 <= ma <= MAX_ATTEMPTS_LIMIT:
            errors.append(f"max_attempts {ma} out of bounds (1..{MAX_ATTEMPTS_LIMIT})")
    model = data.get("model", DEFAULT_MODEL)
    if not isinstance(model, str) or "/" not in model:
        errors.append(f"model {model!r} is not a valid provider/model identifier")
    return errors


def decide(
    *,
    event: str,
    action: str = "",
    issue_number: int = 0,
    issue_labels: list[str],
    issue_body: str,
    issue_author_assoc: str,
    comment_body: str = "",
    commenter_assoc: str = "",
    sender_is_bot: bool = False,
    repo: str,
) -> dict:
    """Decide what the worker should do for a webhook event.

    Returns a dict with at least ``decision`` (one of start/cancel/none),
    ``reason`` and, for start, the task fields needed by the worker.
    """
    out: dict = {"decision": "none", "reason": ""}
    if TASK_LABEL not in issue_labels:
        out["reason"] = "not an ai-task issue"
        return out
    if sender_is_bot:
        out["reason"] = "ignoring bot event (prevents self-trigger loops)"
        return out

    data = parse_task_body(issue_body)
    status = status_from_labels(issue_labels)
    attempts = int(data.get("attempts", 0))
    max_attempts = int(data.get("max_attempts", DEFAULT_MAX_ATTEMPTS))

    if CANCELLED_LABEL in issue_labels or status == "cancelled":
        out["reason"] = "task is cancelled"
        return out

    first_line = (comment_body or "").strip().splitlines()
    first_line = first_line[0].strip() if first_line else ""

    if event == "issue_comment":
        if first_line.lower().startswith("/cancel"):
            if is_trusted(commenter_assoc):
                out.update(decision="cancel", reason="/cancel by trusted user")
            else:
                out["reason"] = "/cancel by untrusted user ignored"
            return out
        if first_line.lower().startswith("/retry"):
            if not is_trusted(commenter_assoc):
                out["reason"] = "/retry by untrusted user ignored"
                return out
            if not is_trusted(issue_author_assoc):
                out["reason"] = "issue author is not trusted"
                return out
            if status not in RETRYABLE_STATUSES:
                out["reason"] = f"status {status!r} is not retryable"
                return out
            if attempts >= max_attempts:
                out["reason"] = (
                    f"attempt budget exhausted ({attempts}/{max_attempts})"
                )
                return out
            errors = validate_task(data, repo)
            if errors:
                out["reason"] = "invalid task fields: " + "; ".join(errors)
                return out
            out.update(
                decision="start",
                reason=f"/retry accepted (attempt {attempts + 1}/{max_attempts})",
                is_retry=True,
                attempts=attempts + 1,
            )
            out.update(_task_fields(data, repo, issue_number))
            return out
        out["reason"] = "ordinary comment, no action"
        return out

    # issues events (opened / labeled / edited / ... )
    if event == "issues":
        if not is_trusted(issue_author_assoc):
            out["reason"] = "issue author is not trusted"
            return out
        if status in FINAL_STATUSES:
            out["reason"] = f"task already {status}"
            return out
        if status == "running":
            out["reason"] = "task already running (duplicate event ignored)"
            return out
        errors = validate_task(data, repo)
        if errors:
            out.update(decision="invalid", reason="; ".join(errors))
            return out
        out.update(
            decision="start",
            reason="new/queued task from trusted author",
            is_retry=False,
            attempts=max(attempts, 1),
        )
        out.update(_task_fields(data, repo, issue_number))
        return out

    out["reason"] = f"unsupported event {event!r}"
    return out


def _task_fields(data: dict, repo: str, issue_number: int = 0) -> dict:
    task_text = (data.get("task") or "").strip()
    return {
        "task_id": data.get("task_id", ""),
        "task_text": task_text,
        "model": data.get("model", DEFAULT_MODEL),
        "max_iterations": int(data.get("max_iterations", DEFAULT_MAX_ITERATIONS)),
        "max_attempts": int(data.get("max_attempts", DEFAULT_MAX_ATTEMPTS)),
        "branch": data.get("branch", "") or branch_name(
            issue_number, task_text[:60]
        ),
        "repo": data.get("repo", repo),
    }


def _cmd_decide(args: argparse.Namespace) -> int:
    event_path = os.environ.get("GITHUB_EVENT_PATH", "")
    try:
        with open(event_path, encoding="utf-8") as fh:
            event_payload = json.load(fh)
    except (OSError, json.JSONDecodeError) as exc:
        print(f"cannot read event payload: {exc}", file=sys.stderr)
        return 2
    event = os.environ.get("GITHUB_EVENT_NAME", "")
    issue = event_payload.get("issue", {})
    comment = event_payload.get("comment", {})
    sender = event_payload.get("sender", {})
    result = decide(
        event=event,
        action=event_payload.get("action", ""),
        issue_number=int(issue.get("number", 0) or 0),
        issue_labels=[l.get("name", "") for l in issue.get("labels", [])],
        issue_body=issue.get("body", ""),
        issue_author_assoc=(issue.get("author_association") or ""),
        comment_body=comment.get("body", "") if comment else "",
        commenter_assoc=(comment.get("author_association") or "") if comment else "",
        sender_is_bot=(sender.get("type") or "") == "Bot",
        repo=os.environ.get("GITHUB_REPOSITORY", ""),
    )
    out_path = os.environ.get("GITHUB_OUTPUT", "")
    lines = []
    for key in (
        "decision",
        "reason",
        "task_id",
        "model",
        "max_iterations",
        "max_attempts",
        "branch",
        "attempts",
        "is_retry",
    ):
        if key in result:
            value = result[key]
            if isinstance(value, bool):
                value = "true" if value else "false"
            lines.append(f"{key}={value}")
    text = "\n".join(lines)
    if out_path:
        with open(out_path, "a", encoding="utf-8") as fh:
            fh.write(text + "\n")
    else:
        print(text)
    return 0


def _cmd_update_body(args: argparse.Namespace) -> int:
    with open(args.body_file, encoding="utf-8") as fh:
        body = fh.read()
    updates = json.loads(args.updates_json)
    sys.stdout.write(upsert_task_block(body, updates))
    return 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="cmd", required=True)
    sub.add_parser("decide", help="decide from GITHUB_EVENT_PATH, write GITHUB_OUTPUT")
    upd = sub.add_parser("update-body", help="merge JSON updates into an issue body")
    upd.add_argument("--body-file", required=True)
    upd.add_argument("--updates-json", required=True)
    args = parser.parse_args(argv)
    if args.cmd == "decide":
        return _cmd_decide(args)
    return _cmd_update_body(args)


if __name__ == "__main__":
    raise SystemExit(main())
