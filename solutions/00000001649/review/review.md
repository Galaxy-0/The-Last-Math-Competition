# Solution Review — Conjecture 00000001649 (PR 894)

**Submission:** ziangni-sys — `ziangni-sys_submission_20261008212800`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-10-08

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000001649; the conjecture was open, and the PR changed no conjecture, README, leaderboard, or metadata files.
- **Report and PDF.** I read the complete official conjecture, LaTeX report, and submitted PDF. Two independent LaTeX compilations, `pdfinfo`, and text extraction succeeded.
- **Lean and auxiliary code.** A fresh pinned Lean build succeeded and printed the required axiom audits. Audited theorems use only `propext`, `Classical.choice`, and/or `Quot.sound`. No `sorry`, `native_decide`, custom axiom, unsafe declaration, implementation override, extern, or kernel bypass was found. No unrun auxiliary program was submitted.

## Semantic audit

For n=2 the conjectured top degree is −1, but the formalized group-cochain quotient gives nonzero H⁰(SL₂(ℤ);ℚ), directly contradicting the proposed maximum. The formal definitions and capstone theorem address the exact filed statement rather than a surrogate or assumed conclusion.

## Disposition

APPROVED — the disproof is accepted and PR 894 was merged.
