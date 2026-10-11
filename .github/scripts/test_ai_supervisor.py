#!/usr/bin/env python3
"""Unit tests for ai_supervisor.py. Stdlib only: python3 test_ai_supervisor.py"""

from __future__ import annotations

import unittest

from ai_supervisor import (
    branch_name,
    decide,
    parse_task_body,
    render_task_block,
    slugify,
    status_from_labels,
    upsert_task_block,
    validate_task,
)

REPO = "mahithpaulin/axiom"


def body_of(**fields):
    base = {"task_id": "t1", "task": "Add feature X", "repo": REPO}
    base.update(fields)
    return render_task_block(base) + "\n\nAdd feature X"


class TestSlugify(unittest.TestCase):
    def test_basic(self):
        self.assertEqual(slugify("Implement feature X!"), "implement-feature-x")

    def test_empty(self):
        self.assertEqual(slugify("!!!"), "task")

    def test_truncates(self):
        self.assertLessEqual(len(slugify("a " * 100)), 40)

    def test_branch(self):
        self.assertEqual(branch_name(12, "Fix NPE"), "ai-task/12-fix-npe")


class TestTaskBlock(unittest.TestCase):
    def test_roundtrip(self):
        data = {"task_id": "t1", "status": "queued", "attempts": 1}
        parsed = parse_task_body(render_task_block(data) + "\nbody text")
        self.assertEqual(parsed, data)

    def test_missing_block(self):
        self.assertEqual(parse_task_body("no block here"), {})

    def test_corrupt_block(self):
        self.assertEqual(parse_task_body("<!-- ai-task: not json -->"), {})

    def test_upsert_updates_in_place(self):
        updated = upsert_task_block(body_of(), {"status": "running", "attempts": 1})
        parsed = parse_task_body(updated)
        self.assertEqual(parsed["status"], "running")
        self.assertEqual(parsed["attempts"], 1)
        self.assertIn("Add feature X", updated)  # human text preserved

    def test_upsert_adds_block_when_missing(self):
        updated = upsert_task_block("plain body", {"status": "queued"})
        self.assertEqual(parse_task_body(updated)["status"], "queued")
        self.assertIn("plain body", updated)


class TestStatusLabels(unittest.TestCase):
    def test_reads_status(self):
        self.assertEqual(
            status_from_labels(["ai-task", "ai-status-running"]), "running"
        )

    def test_defaults_to_queued(self):
        self.assertEqual(status_from_labels(["ai-task"]), "queued")

    def test_ignores_unknown(self):
        self.assertEqual(status_from_labels(["ai-status-bogus"]), "queued")


class TestValidate(unittest.TestCase):
    def test_valid(self):
        self.assertEqual(
            validate_task(
                {"task": "do X", "repo": REPO, "max_iterations": 3,
                 "max_attempts": 2, "model": "opencode/space-bunny-free"},
                REPO,
            ),
            [],
        )

    def test_empty_task(self):
        errs = validate_task({"task": "  ", "repo": REPO}, REPO)
        self.assertTrue(any("empty" in e for e in errs))

    def test_wrong_repo(self):
        errs = validate_task({"task": "x", "repo": "evil/fork"}, REPO)
        self.assertTrue(any("does not match" in e for e in errs))

    def test_bounds(self):
        errs = validate_task(
            {"task": "x", "repo": REPO, "max_iterations": 99, "max_attempts": 0},
            REPO,
        )
        self.assertEqual(len(errs), 2)

    def test_bad_model(self):
        errs = validate_task({"task": "x", "repo": REPO, "model": "gpt4"}, REPO)
        self.assertTrue(any("model" in e for e in errs))


class TestDecide(unittest.TestCase):
    def test_new_task_starts(self):
        r = decide(
            event="issues", action="opened",
            issue_labels=["ai-task", "ai-status-queued"],
            issue_body=body_of(), issue_author_assoc="OWNER", repo=REPO,
        )
        self.assertEqual(r["decision"], "start")
        self.assertEqual(r["attempts"], 1)
        self.assertFalse(r["is_retry"])
        self.assertEqual(r["model"], "opencode/space-bunny-free")
        self.assertTrue(r["branch"].startswith("ai-task/0-") or "ai-task/" in r["branch"])

    def test_relabel_retry_consumes_budget(self):
        # Relabeling failed->queued goes through the issues path and must
        # still consume an attempt, or retries would be unlimited.
        r = decide(
            event="issues", action="labeled",
            issue_labels=["ai-task", "ai-status-queued"],
            issue_body=body_of(attempts=1), issue_author_assoc="OWNER",
            repo=REPO,
        )
        self.assertEqual(r["decision"], "start")
        self.assertEqual(r["attempts"], 2)
        self.assertTrue(r["is_retry"])

    def test_issues_path_budget_enforced(self):
        r = decide(
            event="issues", action="labeled",
            issue_labels=["ai-task", "ai-status-queued"],
            issue_body=body_of(attempts=2, max_attempts=2),
            issue_author_assoc="OWNER", repo=REPO,
        )
        self.assertEqual(r["decision"], "none")
        self.assertIn("exhausted", r["reason"])

    def test_untrusted_author_never_starts(self):
        for assoc in ("NONE", "CONTRIBUTOR", "FIRST_TIMER", ""):
            with self.subTest(assoc=assoc):
                r = decide(
                    event="issues", action="opened",
                    issue_labels=["ai-task"],
                    issue_body=body_of(), issue_author_assoc=assoc, repo=REPO,
                )
                self.assertEqual(r["decision"], "none")

    def test_untrusted_submit_with_secret_safe(self):
        # Even a perfectly formed task from a stranger must not start.
        r = decide(
            event="issues", action="opened",
            issue_labels=["ai-task"],
            issue_body=body_of(), issue_author_assoc="NONE", repo=REPO,
        )
        self.assertNotEqual(r["decision"], "start")

    def test_no_label_no_action(self):
        r = decide(
            event="issues", action="opened", issue_labels=[],
            issue_body="hi", issue_author_assoc="OWNER", repo=REPO,
        )
        self.assertEqual(r["decision"], "none")

    def test_duplicate_running_ignored(self):
        r = decide(
            event="issues", action="labeled",
            issue_labels=["ai-task", "ai-status-running"],
            issue_body=body_of(), issue_author_assoc="OWNER", repo=REPO,
        )
        self.assertEqual(r["decision"], "none")

    def test_final_status_ignored(self):
        r = decide(
            event="issues", action="edited",
            issue_labels=["ai-task", "ai-status-completed"],
            issue_body=body_of(), issue_author_assoc="OWNER", repo=REPO,
        )
        self.assertEqual(r["decision"], "none")

    def test_cancelled_never_starts(self):
        r = decide(
            event="issues", action="opened",
            issue_labels=["ai-task", "ai-status-cancelled"],
            issue_body=body_of(), issue_author_assoc="OWNER", repo=REPO,
        )
        self.assertEqual(r["decision"], "none")

    def test_bot_events_ignored(self):
        r = decide(
            event="issues", action="opened",
            issue_labels=["ai-task"],
            issue_body=body_of(), issue_author_assoc="OWNER",
            sender_is_bot=True, repo=REPO,
        )
        self.assertEqual(r["decision"], "none")

    def test_retry_accepted(self):
        r = decide(
            event="issue_comment",
            issue_labels=["ai-task", "ai-status-failed"],
            issue_body=body_of(attempts=1),
            issue_author_assoc="OWNER",
            comment_body="/retry please", commenter_assoc="OWNER", repo=REPO,
        )
        self.assertEqual(r["decision"], "start")
        self.assertTrue(r["is_retry"])
        self.assertEqual(r["attempts"], 2)

    def test_retry_budget_enforced(self):
        r = decide(
            event="issue_comment",
            issue_labels=["ai-task", "ai-status-failed"],
            issue_body=body_of(attempts=2, max_attempts=2),
            issue_author_assoc="OWNER",
            comment_body="/retry", commenter_assoc="OWNER", repo=REPO,
        )
        self.assertEqual(r["decision"], "none")
        self.assertIn("exhausted", r["reason"])

    def test_retry_wrong_status(self):
        r = decide(
            event="issue_comment",
            issue_labels=["ai-task", "ai-status-completed"],
            issue_body=body_of(attempts=1),
            issue_author_assoc="OWNER",
            comment_body="/retry", commenter_assoc="OWNER", repo=REPO,
        )
        self.assertEqual(r["decision"], "none")

    def test_retry_untrusted_commenter(self):
        r = decide(
            event="issue_comment",
            issue_labels=["ai-task", "ai-status-failed"],
            issue_body=body_of(attempts=1),
            issue_author_assoc="OWNER",
            comment_body="/retry", commenter_assoc="NONE", repo=REPO,
        )
        self.assertEqual(r["decision"], "none")

    def test_retry_needs_trusted_author(self):
        r = decide(
            event="issue_comment",
            issue_labels=["ai-task", "ai-status-failed"],
            issue_body=body_of(attempts=1),
            issue_author_assoc="NONE",
            comment_body="/retry", commenter_assoc="OWNER", repo=REPO,
        )
        self.assertEqual(r["decision"], "none")

    def test_ordinary_comment_ignored(self):
        r = decide(
            event="issue_comment",
            issue_labels=["ai-task", "ai-status-running"],
            issue_body=body_of(),
            issue_author_assoc="OWNER",
            comment_body="looks good, thanks!", commenter_assoc="OWNER",
            repo=REPO,
        )
        self.assertEqual(r["decision"], "none")

    def test_cancel_command(self):
        r = decide(
            event="issue_comment",
            issue_labels=["ai-task", "ai-status-running"],
            issue_body=body_of(),
            issue_author_assoc="OWNER",
            comment_body="/cancel", commenter_assoc="MEMBER", repo=REPO,
        )
        self.assertEqual(r["decision"], "cancel")

    def test_duplicate_submission_same_state(self):
        # Relabel / edit events for an already-queued task start it once:
        # the second identical event sees status running and stops.
        first = decide(
            event="issues", action="labeled",
            issue_labels=["ai-task", "ai-status-queued"],
            issue_body=body_of(), issue_author_assoc="OWNER", repo=REPO,
        )
        self.assertEqual(first["decision"], "start")
        second = decide(
            event="issues", action="labeled",
            issue_labels=["ai-task", "ai-status-running"],
            issue_body=body_of(), issue_author_assoc="OWNER", repo=REPO,
        )
        self.assertEqual(second["decision"], "none")


if __name__ == "__main__":
    unittest.main(verbosity=2)
