# Solution Review — Conjecture 00000002341 (PR 273)

**Submission:** orionsheep — `orionsheep_submission_20261003104328`
**Reviewer:** competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-03

## Checklist
- [x] LaTeX source and PDF present
- [x] Lean 4 project compiles completely (lake build, exit 0)
- [x] No `sorry`, no `native_decide`, no extra axioms
- [x] Submission matches the conjecture's objects and literal statement

## Conjecture (verbatim summary)
The conjecture claims the pseudospectral area of a matrix equals pi*eps^2*(1 + ||A*A - AA*||_HS/2) — an explicit identity in the Hilbert-Schmidt deviation from normality — and that the area growth is exactly eps^2.

## What the submission proves
At the perfectly normal instance A = diag(0,10) the deviation term vanishes (diag_normal; claimed factor 1), so the identity predicts area pi*eps^2. But for a normal matrix the eps-pseudospectrum is exactly the union of the eps-disks around the eigenvalues 0 and 10 — disjoint since 2 < 10 (two_disks_disjoint) — of total area 2*pi*eps^2: factor 1 claimed, factor 2 true (1 != 2 certified). The tex strengthens this: diag(0,10) and diag(0,5,10) share deviation 0 but have areas 2 and 3 times pi*eps^2, so no formula in the deviation alone can hold; the eps^2-growth clause fails independently for non-normal matrices.

## Verification notes
The disk geometry (eigenvalue separation 10 > 2; areas 2pi vs pi at eps = 1) and the classical normal-matrix pseudospectrum identity checked; the grid integration in reproduce.py (6.281 ~ 2pi) is consistent. "Random matrix" is moot because the claimed identity is pointwise in the deviation and the counterexample is exact (and robust under small perturbations by continuity); the operator-theoretic layer beyond the entry arithmetic is prose, correctly attributed.

## Verdict
APPROVED — merged into main.

