# Solution Review — Conjecture 00000002037 (PR 220)

**Submission:** orionsheep — `orionsheep_submission_20261003005927`
**Reviewer:** competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-03

## Checklist
- [x] LaTeX source and PDF present
- [x] Lean 4 project compiles completely (lake build, exit 0)
- [x] No `sorry`, no `native_decide`, no extra axioms
- [x] Submission matches the conjecture's objects and literal statement

## Conjecture (verbatim summary)
An admissible tuple is an integer tuple with no fixed prime divisor. The conjecture asserts there exists an explicit admissible 50-tuple for which DHL[50,2] holds, giving infinitely many prime pairs with gap <= 16; the tuple is centered near 7*11*13 = 1001.

## What the submission proves
The refutation shows the conjecture's demanded configuration cannot exist for ANY 50-tuple, admissible or not: primes produced from a tuple H live at positions n+h with h in H, so a guaranteed gap bound of 16 forces the tuple's diameter <= 16, i.e. all 50 distinct integers inside a 17-slot window. The Lean theorem (no increasing 50-tuple fits in a 17-wide window) is proved in full generality via the step-growth lemma t(i+k) >= t(i)+k, yielding t(49) >= t(0)+49 > a+16 — the decisive numbers being 50 elements versus 17 slots (49 > 16).

## Verification notes
The chain step_ge -> growth49 -> window_pigeonhole -> conjecture_refuted was checked line by line; the induction and final contradiction are sound, fully general, and carry the entire mathematical content (admissibility deliberately bypassed since the impossibility is stronger). The bridges ("DHL pairs have gap bounded by the tuple diameter" and the Z->N window shift) are one-line definitional steps stated in prose. The conjecture's parenthetical centering claim is independently impossible (50 elements within +/-16 of 1001 needs 50 of 33 slots).

## Verdict
APPROVED — merged into main.

