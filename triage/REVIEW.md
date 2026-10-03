# Maintainer Review — PR #6 (triage/, rule 5 input)

**Reviewer:** lidangzzz (maintainer), 2026-10-03. **Verdict: MERGED.**

## What was verified

All four verdict scripts run cleanly from this directory and reproduce the
campaign report:

- `target_quick.py` — verdicts A (00000001243), B (00000001016),
  D (00000008540): matches §3.1–3.4, including the C₃ subdirect example.
- `validate_zd.py` — twin-class reduction validated against brute force for
  n ∈ [4, 120]: **0 mismatches**.
- `zerodivisor.py` — verdict C (00000002222): **831** composite n in [4, 1000],
  ω range 1 (n = 4) … 30 (n = 961), largest quotient graph 30 vertices
  (n = 840, ω = 5), **0 counterexamples** to χ = ω. All three corrected figures
  from the PR description are what the script actually prints.
- `target_ef.py` — verdicts E (00000001619) and F (00000001668): matches §3.5,
  including the Brooks-theorem structural argument and the pentagonal-prism
  counterexample G(5,1) with χ_c = 5/2.

`triage.md` was regenerated with `triage.py` and is **byte-identical** to the
committed file when paired with the rule-2 artifacts of the matching revision
(features v1.1 + `metadata.scored.csv` v1.1, i.e. the 1,238-candidate pool the
ranking consumed).

## Known drift (documented, not blocking)

The rule-2 pass in `../scoring/` has since regenerated its scores (v1.2, after
the ID-leakage fix). Under v1.2 the `disproof_difficulty ≤ 2` pool is **995**
rows rather than 1,238, so re-running the ranking today yields a different
top-45. The campaign report's verdicts are unaffected — each is reproduced by a
self-contained script over specific conjectures — but the ranking table should
be read as computed against the v1.1 scores it cites. A refreshed ranking
against v1.2 is straightforward to produce if rule 5 needs it.

## Disposition

- Verdicts A, D, F were packaged as the rule-3 submissions already merged
  (conjectures 00000001243, 00000008540, 00000001668).
- Verdicts B and E statements are ill-posed and are correctly not submitted.
- Verdict C (00000002222, χ = ω for Γ(ℤₙ), n ≤ 1000) is a **confirmed-open**
  conjecture: it stays open in the leaderboard. A complete proof would need the
  exhaustive 831-case computation formalized in Lean; contributors are welcome
  to attempt it.
- This is a rule-5 strategy artifact, not a problem submission; it does not
  affect the leaderboard.
