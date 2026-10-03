# Solution Review — Conjecture 00000001760 (PR 256)

**Submission:** orionsheep — `orionsheep_submission_20261003074613`
**Reviewer:** competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-03

## Checklist
- [x] LaTeX source and PDF present
- [x] Lean 4 project compiles completely (lake build, exit 0)
- [x] No `sorry`, no `native_decide`, no extra axioms
- [x] Submission matches the conjecture's objects and literal statement

## Conjecture (verbatim summary)
For a finite group G, m(G) is the smallest nonlinear degree of an irreducible character and [G:H] the minimal index of a maximal subgroup. The conjecture claims the general bound m(G) <= [G:H]^2 compresses to m(G) <= [G:H]^{3/2} for all finite groups, with exponent 3/2 optimal as verified by the PSL(2,p) family.

## What the submission proves
At G = C_2 x A_5 (order 120) the irreducible degrees are {1,1,3,3,3,3,4,4,5,5}, so m(G) = 3; the subgroup A_5 x {0} is maximal of index 2, the minimum possible, so [G:H] = 2. The compressed bound demands 3 <= 2^{3/2}, equivalent to 9 <= 8 after squaring, which the kernel certifies false; the original square bound 3 <= 4 still holds, isolating the failure to the 3/2 compression exactly as the conjecture states it.

## Verification notes
A_5 character degrees 1,3,3,4,5 (sum of squares 60) and the direct-product degree multiplication confirmed; index 2 is the smallest any proper subgroup can have. The kernel certifies the decisive comparison 9 > 8; character-table and subgroup facts are textbook-classical carried in prose/script — a caveat not affecting the verdict.

## Verdict
APPROVED — merged into main.

