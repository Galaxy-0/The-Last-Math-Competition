# Maintainer Review — PR #5 (scoring/, rule 2)

**Reviewer:** lidangzzz (maintainer), 2026-10-03. **Verdict: MERGED.**

## What was verified

Reproduced end-to-end from a clean checkout of the PR branch, following the
README exactly:

- `extract_features.py` run in 4 chunks of 2,500 over all 10,000 conjecture
  files; concatenated; `score_conjectures.py` run against `metadata.csv`.
- `out/metadata.scored.csv` and `out/review_queue.csv` are **byte-identical**
  to the committed `scoring/metadata.scored.csv` and `scoring/review_queue.csv`.
- Confidence bands reproduce exactly: high 8972 / medium 1001 / low 27.
- Schema discipline verified programmatically: header identical to
  `metadata.csv`, id order identical, **0 differences in any non-score column**,
  all 10,000 rows carry all five scores, and the 7 `well_definedness_level = 0`
  rows are present in the data.

## Correction applied at merge time

The committed `README.md` results table and the `scoring_report.md`
`disproof_difficulty` section still carried the **v1.1** distribution
(145 / 1093 / 2470 / 5019 / 1273, mean 3.62). The committed CSVs are the **v1.2**
regeneration (commit "Fix ID leakage into numeric features"), whose actual
distribution is:

| `disproof_difficulty` | 1 | 2 | 3 | 4 | 5 | median | mean |
|---|---|---|---|---|---|---|---|
| count | 140 | 855 | 2249 | 5346 | 1410 | 4.0 | 3.70 |

All other dimension tables in both documents already match the v1.2 data. The
two stale tables were updated to the numbers above; the CSVs were not touched.
The qualitative finding (median proof_difficulty 2 < median disproof_difficulty
4) is unchanged.

## Scope notes

- The five score columns of `metadata.csv` remain as maintained by the
  organizers; folding scores in is deferred by design (see the PR's "Where
  these numbers should live"). The `novelty` column carries the documented
  structural caveat — treat it as a lower bound at best.
- This is a rule-2 evaluation artifact, not a problem submission; it does not
  affect the leaderboard.
