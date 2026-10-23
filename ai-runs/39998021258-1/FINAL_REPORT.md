# Axiom v4 AI optimization campaign `39998021258-1`

- Repository: `mahithpaulin/axiom` (target branch `v4`)
- Campaign branch: `ai-optimization/run2-axiom-v4`
- Started: 2026-10-23T17:48:25Z
- Finished: 2026-10-23T18:01:02Z
- Wall time: 12.609 min of 225.0 budgeted
- Iterations: 8 (5 accepted, 1 rejected)
- Head: `5d00e218e27bfa4fe2baf717fce9ea6190a9827d`

## Status

- Driver status: finished
- Blocked reason: none
- Crash: none

## Baseline

- Commit: `a54aea4f6fea2e347c0360827aa570538eac77ea`
- Tests: 274 passed, 0 failed (9.584s)
- Benchmark rows: 19 (best of 2 runs, 56.32s)

## Model access

- `OPENCODE_API_KEY` present: True
- Free candidates: opencode/deepseek-v4.1-flash-free, opencode/cat-jam-free, opencode/glm-5.3-flash-free, opencode/ll-alpha-free, opencode/longcat-2.5-preview-free, opencode/mimo-v2.6-flash-free, opencode/muse-spark-1.3-contributor-free, opencode/nemotron-3-ultra-free, opencode/nemotron-3.5-lightning-free, opencode/nemotron-3.5-super-vl-free, opencode/space-bunny-free
- Calls: 1; failures: 0
- Status: opencode/deepseek-v4.1-flash-free rejected the free-tier request
- Push failures: 0

## Accepted changes

| Task | Iteration | Commit | Tests | Benchmark |
|---|---:|---|---:|---|
| `A001-peak-rss` | 1 | `ec20a342ce23` | 275 | not run |
| `A002-smt-negation` | 2 | `ecf13da2f01d` | 277 | not run |
| `A003-fol-equality-negative` | 3 | `9a119ae7e228` | 279 | not run |
| `A004-planning-negative-precondition` | 4 | `4c3817cf7bfb` | 281 | not run |
| `A005-docs-peak-rss` | 5 | `a4c64f1a8f0b` | 281 | not run |

## Rejected or blocked work

- Iteration 6 `A006-db-third-index`: CampaignError: opencode/deepseek-v4.1-flash-free rejected the free-tier request

## Measured benchmark comparison

| Row | Baseline ms | Final ms | Wall ratio | Baseline rss kB | Final rss kB | RSS ratio |
|---|---:|---:|---:|---:|---:|---:|
| `hash_cons_1000_terms` | 0.99 | 1.08 | 1.091 | 2780 | 3052 | 1.098 |
| `hash_cons_sharing` | 0.01 | 0.01 | 1.000 | 2780 | 3052 | 1.098 |
| `unify_ground_pairs` | 50.03 | 50.07 | 1.001 | 3328 | 3324 | 0.999 |
| `match_pattern_vs_fact` | 50.00 | 50.00 | 1.000 | 3328 | 3324 | 0.999 |
| `occurs_check_cost` | 50.00 | 50.00 | 1.000 | 3328 | 3324 | 0.999 |
| `db_index_lookup` | 50.53 | 50.59 | 1.001 | 12568 | 12564 | 1.000 |
| `db_index_lookup_arg1` | 52.24 | 52.15 | 0.998 | 12568 | 12564 | 1.000 |
| `db_scan_lookup` | 815.48 | 816.33 | 1.001 | 12568 | 12564 | 1.000 |
| `semi_naive_vs_fixpoint_n600[A]` | 792.34 | 851.16 | 1.074 | 55456 | 55456 | 1.000 |
| `semi_naive_vs_fixpoint_n600[B]` | 820.11 | 844.27 | 1.029 | 55456 | 55456 | 1.000 |
| `tc_path_n200` | 19.02 | 19.18 | 1.008 | 23604 | 55456 | 2.349 |
| `tc_path_n1000` | 969.21 | 1014.56 | 1.047 | 6240 | 154340 | 24.734 |
| `tc_random_n1500` | 15789.91 | 16514.54 | 1.046 | 8284 | 675920 | 81.593 |
| `stratified_negation_5000` | 8.62 | 10.52 | 1.220 | 9140 | 675920 | 73.952 |
| `proof_verify_strong` | 50.02 | 50.02 | 1.000 | 9176 | 675920 | 73.662 |
| `proof_verify_shallow` | 0.07 | 0.07 | 1.000 | 9176 | 675920 | 73.662 |
| `memory_per_fact_probe` | 556.78 | 702.14 | 1.261 | 62756 | 675920 | 10.771 |
| `parse_program` | 50.01 | 50.00 | 1.000 | 62756 | 675920 | 10.771 |
| `end_to_end_prove` | 53.32 | 53.76 | 1.008 | 62760 | 675920 | 10.770 |

Best-of-two wall times on a shared runner; treat ratios as diagnostic, not a performance claim. Deterministic counters in the bench log are the stronger signal.

## Verification

- Final full suite: ok=True passed=281 failed=0 ignored=0
- Clippy/format gate: every accepted change ran both; rejected changes were reset.
- No push to the target branch, no merge, no release, no workflow or permission edit.
- Model output was treated as untrusted and applied only through the validated edit path.

## Unresolved defects and next steps

- Blocked on model availability: `A006-db-third-index`, `A007-smt-lib-printer`, `A008-datalog-join-order`, `A009-fol-equality-coverage`, `A010-docs-claim-audit`, `A011-rdl-chain-memory`
- Continue from the backlog in `targets/axiom-v4/backlog.json`.
- Review every accepted commit; no automatic merge is performed.
- Re-run with `workflow_dispatch` after the workflow reaches the default branch.

## Safety notes

- The model never received edit, bash, network, or repository credentials.
- All writes went through the manifest allowlist and diff checks.
- Tests were not weakened; a full-suite pass and a non-decreasing test count were required.
- Logs are redacted for token-shaped strings and for the configured secret values.
