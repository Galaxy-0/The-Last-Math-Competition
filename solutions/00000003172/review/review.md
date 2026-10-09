# Solution Review — Conjecture 00000003172 (PR 901)

**Submission:** ziangni-sys — `ziangni-sys_submission_20261008193000`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-10-08

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000003172; the conjecture was open, and the PR changed no conjecture, README, leaderboard, or metadata files.
- **Report and PDF.** I read the complete official conjecture, LaTeX report, and submitted PDF. Two independent LaTeX compilations, `pdfinfo`, and text extraction succeeded.
- **Lean and auxiliary code.** A fresh pinned Lean build succeeded and printed the required axiom audits. Audited theorems use only `propext`, `Classical.choice`, and/or `Quot.sound`. No `sorry`, `native_decide`, custom axiom, unsafe declaration, implementation override, extern, or kernel bypass was found. No unrun auxiliary program was submitted.

## Semantic audit

Actual one-sparse IHT for f(x,y)=x²/2 converges geometrically with ratio 1/2 to a sparse global minimizer/solution-set point, while every positive restricted-curvature constant fails on the flat sparse y-axis; this disproves necessity. The formal definitions and capstone theorem address the exact filed statement rather than a surrogate or assumed conclusion.

## Disposition

APPROVED — the disproof is accepted and PR 901 was merged.
