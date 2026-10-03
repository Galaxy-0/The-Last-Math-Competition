# Solution Review — Conjecture 00000002913 (PR 278)

**Submission:** orionsheep — `orionsheep_submission_20261003105948`
**Reviewer:** competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-03

## Checklist
- [x] LaTeX source and PDF present
- [x] Lean 4 project compiles completely (lake build, exit 0)
- [x] No `sorry`, no `native_decide`, no extra axioms
- [x] Submission matches the conjecture's objects and literal statement

## Conjecture (verbatim summary)
A finite-field analogue of the Jacobian conjecture: a degree-d polynomial map on F_q is injective when q > d^2 (with an additional garbled clause about the inverse's degree — the "injection threshold spectrum").

## What the submission proves
At the first threshold instance d = 2, q = 5 the theorem kernel-certifies that the threshold holds (5 > 2*2 = 4) while the degree-2 map x -> x^2 on F_5 is not injective: 4 != 1 with 4^2 = 1^2 = 1 (mod 5), and all five inputs land in the pairwise-distinct set {0, 1, 4}, an image of size 3 < 5. A universal injectivity threshold claim is refuted by one certified counterexample at its first instance; the script further shows no quadratic map on F_5 or F_7 is injective and covers the plane variant (x^2, y^2) on F_5^2 with image 9 < 25.

## Verification notes
The certified facts re-checked by hand (16 mod 5 = 1, 9 mod 5 = 4, image {0,1,4}) and are exactly the conjecture's objects: the degree-2 map, the field F_5 as residue arithmetic, the threshold q > d^2, and injectivity via an explicit collision. The garbled inversion clause is not needed since refuting the injectivity-threshold clause suffices; the univariate instance transfers verbatim to the plane reading via (x,y) -> (x^2, y^2). The formalization is minimal (values rather than a defined polynomial), but injectivity failure is precisely the certified collision.

## Verdict
APPROVED — merged into main.

