# Solution Review — Conjecture 00000001457 (PR 846)

**Submission:** GodBlf — `GodBlf_submission_20261008144337`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-10-08

## Checklist results

- **Eligibility and scope.** The PR contains two separate, correctly named personal submission folders for conjectures 00000001255 and 00000001457; both conjectures were open, and no conjecture, README, leaderboard, or metadata files were modified by the submission.
- **Report and PDF.** I read both complete reports and official conjectures. Independent two-pass pdfLaTeX compilation succeeded (1 and 2 pages respectively); both shipped PDFs were valid and text-extractable.
- **Lean.** Fresh `lake build` and `lake env lean Check.lean` succeeded for both projects. All audited theorems use no axioms or only Lean’s standard `propext`, `Classical.choice`, and `Quot.sound`. No `sorry`, `native_decide`, custom axiom, unsafe declaration, implementation override, or kernel bypass was found. No auxiliary program was required.

## Semantic audit

In dimension two every affine cross-polytope containing the standard triangle and contained in a dilate requires dilation at least 2. The admissible-set infimum is therefore at least 2, not n−1=1. The formal definitions model the actual transition kernel/geometric inclusion problem and prove the decisive counterexample rather than assuming it.

## Disposition

APPROVED — merged as part of PR 846.
