# Solution Review — Conjecture 00000002313 (PR 272)

**Submission:** orionsheep — `orionsheep_submission_20261003103711`
**Reviewer:** competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-03

## Checklist
- [x] LaTeX source and PDF present
- [x] Lean 4 project compiles completely (lake build, exit 0)
- [x] No `sorry`, no `native_decide`, no extra axioms
- [x] Submission matches the conjecture's objects and literal statement

## Conjecture (verbatim summary)
The conjecture claims the second coefficient of the restricted Burnside asymptotics: log|R(r,p)| = (r-1)^2 log p + c_{r,p}, with c of the explicit -log 2 type, the coefficient coming from a corrected Witt formula for Lie algebras.

## What the submission proves
At r = 2 the claimed form reads log|R(2,p)| = log p + c with c of -log 2 type, forcing |R(2,p)| <= 2p. The published orders of the actual restricted Burnside groups dwarf this: |R(2,5)| = 5^34 and |R(2,7)| = 7^20416. Lean certifies the contradiction without evaluating the huge powers: structural exponent monotonicity gives 14 < 7^20416 (R27_dwarfs), 5^34 > 10 (R25_dwarfs), and the exponent gap 1 + 20415 = 20416 — the "constant" c_{2,7} would have to contribute a factor of 7^20415, flatly incompatible with a -log 2-type term.

## Verification notes
5^34 = 582076609134674072265625 (24 digits) and the digit count of 7^20416 (17,254) recomputed, both matching the tex; R(2,5) = 5^34 and R(2,7) = 7^20416 are the landmark power-commutator computations of Havas-Newman-O'Brien and Havas-Vaughan-Lee, correctly cited. Caveat: the published orders are cited rather than proven in Lean — unavoidable for massive computational group theory results — but the comparison arithmetic deriving the contradiction is kernel-certified, and an identity claimed for all (r,p) is refuted at instances.

## Verdict
APPROVED — merged into main.

