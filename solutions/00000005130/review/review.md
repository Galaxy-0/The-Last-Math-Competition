# Solution Review — Conjecture 00000005130 (PR 900)

**Submission:** ziangni-sys — `ziangni-sys_submission_20261008191236`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-10-08

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000005130; the conjecture was open, and the PR changed no conjecture, README, leaderboard, or metadata files.
- **Report and PDF.** I read the complete official conjecture, LaTeX report, and submitted PDF. Two independent LaTeX compilations, `pdfinfo`, and text extraction succeeded.
- **Lean and auxiliary code.** A fresh pinned Lean build succeeded and printed the required axiom audits. Audited theorems use only `propext`, `Classical.choice`, and/or `Quot.sound`. No `sorry`, `native_decide`, custom axiom, unsafe declaration, implementation override, extern, or kernel bypass was found. No unrun auxiliary program was submitted.

## Semantic audit

diag(1,2) and diag(2,1) have identical preconditioner, preconditioned-system, and iteration spectra, but the same Richardson problem and start yield different first iterates; a quarter-turn gives the explicit trajectory relation. The formal definitions and capstone theorem address the exact filed statement rather than a surrogate or assumed conclusion.

## Disposition

APPROVED — the proof is accepted and PR 900 was merged.
