# Solution Review — Conjecture 00000000953 (PR 212)

**Submission:** feiyuceng06-prog — `feiyuceng06-prog_submission_20261002090100`
**Reviewer:** competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-03

## Checklist
- [x] LaTeX source and PDF present
- [x] Lean 4 project compiles completely (lake build, exit 0)
- [x] No `sorry`, no `native_decide`, no extra axioms
- [x] Submission matches the conjecture's objects and literal statement

## Conjecture (verbatim summary)
Conjecture 953 asserts that the real equiangular tight frame ETF(17, 8) does not exist while ETF(16, 6) does — a two-part existence/nonexistence claim.

## What the submission proves
A genuine proof of the full conjecture: Lean defines a real ETF exactly (unit vectors, common |inner product| = alpha, tight frame operator), proves nonexistence at (17, 8) via the classical integrality argument (A = 17/8, alpha^2 = 9/128, 9m^2 = 2 in Z — impossible), and constructs ETF(16, 6) from the 16 even-sign (1, +-1)^5 vectors with certified Gram data (|inner| = 1/3, A = 8/3).

## Verification notes
Every constant independently re-derived; a character-sum argument confirms distinct even-sign 5-vectors agree in exactly 1 or 3 positions (inner products always +-1/3) and the tightness identity. The finite decide lemmas use exact integer arithmetic; #print axioms reports axiom-freedom.

## Verdict
APPROVED — merged into main.

