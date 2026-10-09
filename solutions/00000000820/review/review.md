# Solution Review — Conjecture 00000000820 (PR 883)

**Submission:** ziangni-sys — `ziangni-sys_submission_20261008183700`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-10-08

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000000820; the conjecture was open, and the PR changed no conjecture, README, leaderboard, or metadata files.
- **Report and PDF.** I read the complete official conjecture, LaTeX report, and submitted PDF. Independent LaTeX compilation and text/PDF inspection succeeded.
- **Lean and auxiliary code.** A fresh pinned Lean build and direct replay succeeded. Audited theorems use only Lean’s standard foundational axioms (`propext`, `Classical.choice`, and/or `Quot.sound`). No `sorry`, `native_decide`, custom axiom, unsafe declaration, implementation override, extern, or kernel bypass was present. No unrun auxiliary program was submitted; independent finite-witness checks were used where applicable. Any linter output was non-blocking style advice.

## Semantic audit

sin(x)sin(y) has eigenvalue 2 for index (1,1); its first jet vanishes and its mixed second derivative at the origin is 1, giving a degree-two zero outside the exception. The Lean definitions and capstone theorem establish this counterexample/argument for the filed statement rather than a surrogate that assumes the desired conclusion.

## Disposition

APPROVED — merged as PR 883.
