# Solution Review — Conjecture 00000001749 (PR 255)

**Submission:** orionsheep — `orionsheep_submission_20261003074320`
**Reviewer:** competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-03

## Checklist
- [x] LaTeX source and PDF present
- [x] Lean 4 project compiles completely (lake build, exit 0)
- [x] No `sorry`, no `native_decide`, no extra axioms
- [x] Submission matches the conjecture's objects and literal statement

## Conjecture (verbatim summary)
A simultaneous Thue equation is a system F(x,y) = a, G(x,y) = b of two binary homogeneous forms of degree >= 3. The conjecture asserts that the number of solutions is at most (deg F)(deg G), with the bound optimal when the composite root structures are of cyclotomic type.

## What the submission proves
It takes G = 2F with F(x,y) = xy(x+y) and (a, b) = (195093360, 2a), so the system is equivalent to the single Thue equation xy(x+y) = 195093360 while both forms still have degree 3, making the conjectured bound 9. The Lean kernel certifies (by decide) ten integer solutions, e.g. (-2448, 33), together with their distinctness and 9 < 10, so the bound is violated; the script's exhaustive divisor enumeration gives 66 solutions in total.

## Verification notes
All integer solutions independently re-enumerated via signed-divisor/discriminant search: exactly 66 exist; all ten certified pairs evaluate correctly and are pairwise distinct. The pair (F, 2F) literally satisfies the stated hypothesis (proportionality is not excluded by the literal statement, acknowledged in the README boundary section). The ten kernel-certified instances alone already exceed the bound 9, which is all a disproof needs.

## Verdict
APPROVED — merged into main.

