# Axiom v4 AI optimization campaign `39994744230-2`

- Repository: `mahithpaulin/axiom` (target branch `v4`)
- Campaign branch: `ai-optimization/setup-axiom-v4`
- Started: 2026-10-23T17:33:21Z
- Finished: 2026-10-23T17:45:18Z
- Wall time: 11.948 min of 225.0 budgeted
- Iterations: 7 (3 accepted, 2 rejected)
- Head: `c59d4103d1e4112563e14cc135c58b98a9a9ea4b`

## Status

- Driver status: finished
- Blocked reason: none
- Crash: none

## Baseline

- Commit: `5a70ea27819af1bc5969be6a1528506e0990f4a7`
- Tests: 274 passed, 0 failed (7.203s)
- Benchmark rows: 19 (best of 2 runs, 41.922s)

## Model access

- `OPENCODE_API_KEY` present: True
- Free candidates: opencode/deepseek-v4.1-flash-free, opencode/cat-jam-free, opencode/glm-5.3-flash-free, opencode/ll-alpha-free, opencode/longcat-2.5-preview-free, opencode/mimo-v2.6-flash-free, opencode/muse-spark-1.3-contributor-free, opencode/nemotron-3-ultra-free, opencode/nemotron-3.5-lightning-free, opencode/nemotron-3.5-super-vl-free, opencode/space-bunny-free
- Calls: 1; failures: 0
- Status: opencode/deepseek-v4.1-flash-free rejected the free-tier request
- Push failures: 0

## Accepted changes

| Task | Iteration | Commit | Tests | Benchmark |
|---|---:|---|---:|---|
| `A002-smt-negation` | 2 | `79a9d5760773` | 276 | not run |
| `A003-fol-equality-negative` | 3 | `1c9b0437ec18` | 278 | not run |
| `A004-planning-negative-precondition` | 4 | `02131e2bba57` | 280 | not run |

## Rejected or blocked work

- Iteration 1 `A001-peak-rss`: CampaignError: targeted test command failed; full workspace tests failed; test count fell from 274 to 67
- Iteration 5 `A006-db-third-index`: CampaignError: opencode/deepseek-v4.1-flash-free rejected the free-tier request

## Measured benchmark comparison

| Row | Baseline ms | Final ms | Wall ratio | Baseline rss kB | Final rss kB | RSS ratio |
|---|---:|---:|---:|---:|---:|---:|
| `hash_cons_1000_terms` | 0.78 | 0.81 | 1.038 | 2780 | 2772 | 0.997 |
| `hash_cons_sharing` | 0.01 | 0.01 | 1.000 | 2780 | 2772 | 0.997 |
| `unify_ground_pairs` | 50.05 | 50.06 | 1.000 | 3328 | 3320 | 0.998 |
| `match_pattern_vs_fact` | 47.72 | 47.77 | 1.001 | 3328 | 3320 | 0.998 |
| `occurs_check_cost` | 50.03 | 50.05 | 1.000 | 3328 | 3320 | 0.998 |
| `db_index_lookup` | 51.07 | 51.22 | 1.003 | 12568 | 12560 | 0.999 |
| `db_index_lookup_arg1` | 50.62 | 50.67 | 1.001 | 12568 | 12560 | 0.999 |
| `db_scan_lookup` | 654.68 | 653.77 | 0.999 | 12568 | 12560 | 0.999 |
| `semi_naive_vs_fixpoint_n600[A]` | 583.60 | 607.60 | 1.041 | 55372 | 55424 | 1.001 |
| `semi_naive_vs_fixpoint_n600[B]` | 568.69 | 594.95 | 1.046 | 55372 | 55424 | 1.001 |
| `tc_path_n200` | 15.57 | 15.65 | 1.005 | 23604 | 23596 | 1.000 |
| `tc_path_n1000` | 698.66 | 718.28 | 1.028 | 6240 | 6232 | 0.999 |
| `tc_random_n1500` | 11206.91 | 11778.92 | 1.051 | 8284 | 8276 | 0.999 |
| `stratified_negation_5000` | 8.41 | 8.56 | 1.018 | 9140 | 9132 | 0.999 |
| `proof_verify_strong` | 50.02 | 50.00 | 1.000 | 9176 | 9168 | 0.999 |
| `proof_verify_shallow` | 0.05 | 0.06 | 1.200 | 9176 | 9168 | 0.999 |
| `memory_per_fact_probe` | 421.26 | 451.21 | 1.071 | 62756 | 62748 | 1.000 |
| `parse_program` | 50.01 | 50.04 | 1.001 | 62756 | 62748 | 1.000 |
| `end_to_end_prove` | 50.99 | 50.80 | 0.996 | 62760 | 62752 | 1.000 |

Best-of-two wall times on a shared runner; treat ratios as diagnostic, not a performance claim. Deterministic counters in the bench log are the stronger signal.

## Verification

- Final full suite: ok=True passed=280 failed=0 ignored=0
- Clippy/format gate: every accepted change ran both; rejected changes were reset.
- No push to the target branch, no merge, no release, no workflow or permission edit.
- Model output was treated as untrusted and applied only through the validated edit path.

## Unresolved defects and next steps

- Failed tasks worth human review: `A001-peak-rss`
- Blocked on model availability: `A006-db-third-index`, `A007-smt-lib-printer`, `A008-datalog-join-order`, `A009-fol-equality-coverage`, `A010-docs-claim-audit`, `A011-rdl-chain-memory`
- Continue from the backlog in `targets/axiom-v4/backlog.json`.
- Review every accepted commit; no automatic merge is performed.
- Re-run with `workflow_dispatch` after the workflow reaches the default branch.

## Safety notes

- The model never received edit, bash, network, or repository credentials.
- All writes went through the manifest allowlist and diff checks.
- Tests were not weakened; a full-suite pass and a non-decreasing test count were required.
- Logs are redacted for token-shaped strings and for the configured secret values.
