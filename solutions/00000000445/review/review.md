# Solution Review — Conjecture 00000000445 (PR 247)

**Submission:** orionsheep — `orionsheep_submission_20261003062258`
**Reviewer:** competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-03

## Checklist
- [x] LaTeX source and PDF present
- [x] Lean 4 project compiles completely (lake build, exit 0)
- [x] No `sorry`, no `native_decide`, no extra axioms
- [x] Submission matches the conjecture's objects and literal statement

## Conjecture (verbatim summary)
For Solomon's descent algebra Sigma_n, the conjecture asserts that the dimension of its peak subalgebra equals the Euler zigzag number, with a parenthetical claiming this is verifiable for n <= 8.

## What the submission proves
The main Lean theorem certifies that no quadruple of letters can peak at both adjacent positions 2 and 3 (so S_4 has at most the three peak sets {}, {2}, {3}), that all three are attained (by permutations 1234, 1324, 1243), and that 3 < 5. Via the classical Bergeron-Mykytiuk-Sottile-van Willigenburg basis theorem (dim peak algebra = number of peak sets), dim(peak subalgebra of S_4) = 3 while the Euler zigzag number is E_4 = 5, so the conjectured identity fails at n = 4 — squarely inside the claimed n <= 8 verification range.

## Verification notes
Peak sets of S_4..S_8 independently recomputed (3, 5, 8, 13, 21 — the Fibonacci count) against zigzag numbers (5, 16, 61, 272, 1385); they diverge already at n = 4, confirming both the counterexample and that the conjecture's parenthetical is itself false. reproduce.py brute-forces all 24 permutations of S_4, obtaining exactly the three certified peak sets. The descent algebra itself is not formalized (impractical without Mathlib); the two bridging identifications are classical, correct, and honestly flagged in the tex boundary section; the nontrivial combinatorial core is fully kernel-certified.

## Verdict
APPROVED — merged into main.

