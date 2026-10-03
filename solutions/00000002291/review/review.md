# Solution Review — Conjecture 00000002291 (PR 271)

**Submission:** orionsheep — `orionsheep_submission_20261003103259`
**Reviewer:** competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-03

## Checklist
- [x] LaTeX source and PDF present
- [x] Lean 4 project compiles completely (lake build, exit 0)
- [x] No `sorry`, no `native_decide`, no extra axioms
- [x] Submission matches the conjecture's objects and literal statement

## Conjecture (verbatim summary)
The conjecture claims the exact constant c = 1/8 in the centralizer lower bound |C_G(x)| >= c*|G|^{1/2} for simple groups, and that c is tight, attained by low-order simple groups such as involutions of A_5.

## What the submission proves
Two independent refutations, both kernel-certified by exact integer arithmetic. (i) The bound fails: for G = PSL(2,139) and x the image of a non-split torus generator, |G| = 1,342,740 and the centralizer is the torus itself, of order 70; Lean certifies 64*70^2 = 313,600 < 1,342,740 (bound_violated), i.e. 70 < (1/8)sqrt(|G|). (ii) Tightness fails: A_5's centralizer orders are exactly {60, 4, 3, 5} (A5_classes by orbit-stabilizer), no order gives 64|C|^2 = 60 (no_attainment), and at the conjecture's own example the bound holds with strict slack (involution_slack).

## Verification notes
|PSL(2,139)| = 1,342,740 recomputed; A_5 centralizer census brute-forced over all 60 even permutations ({60:1, 4:15, 3:20, 5:24}); verified in F_139[u]/(u^2-2) that 2 is a non-residue mod 139 and zeta = 3+2u has norm 1 and order exactly 140, so the image has order 70 with centralizer 70. The group-theoretic inputs (PSL(2,q) order formula, self-centralizing non-split tori) are classical and stated in prose; the falsifying inequality and the A_5 arithmetic — the decisive content — are kernel-certified.

## Verdict
APPROVED — merged into main.

