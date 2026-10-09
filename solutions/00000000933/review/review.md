# Solution Review — Conjecture 00000000933 (PR 878)

**Submission:** ziangni-sys — `ziangni-sys_submission_20261008182000`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-10-08

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000000933; the conjecture was open, and the PR changed no conjecture, README, leaderboard, or metadata files.
- **Report and PDF.** I read the complete official conjecture, LaTeX report, and submitted PDF. Independent LaTeX compilation and text/PDF inspection succeeded.
- **Lean and auxiliary code.** A fresh pinned Lean build and direct replay succeeded. Audited theorems use only Lean’s standard foundational axioms (`propext`, `Classical.choice`, and/or `Quot.sound`). No `sorry`, `native_decide`, custom axiom, unsafe declaration, implementation override, extern, or kernel bypass was present. No unrun auxiliary program was submitted; independent finite-witness checks were used where applicable. Any linter output was non-blocking style advice.

## Semantic audit

Nonnormal operators have fixed spectrum {0,1} and spectral gap 1, while both nontrivial Riesz projections have norms at least |k|; the relevant infimum is unbounded at fixed gap. The Lean definitions and capstone theorem establish this counterexample/argument for the filed statement rather than a surrogate that assumes the desired conclusion.

## Disposition

APPROVED — merged as PR 878.
