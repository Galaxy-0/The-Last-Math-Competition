# Solution Review — Conjecture 00000002226 (PR 479)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261004150935`
**Reviewer:** independent competition reviewer (structure + build + semantic audit)
**Date:** 2026-10-04

## Checklist results
- Conjecture read: yes — the official bilingual statement asks whether `M_n(R)` over a commutative ring has the McCoy property exactly when `n = 1`. `SOURCE.md` is byte-identical to `conjectures/00000002226.md`.
- Path policy: pass — only the submitter's own new folder was added; base metadata is unsolved.
- LaTeX: independently rebuilt from a fresh copy with `latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex`; exit 0, zero errors, 3 pages. All report and PDF text was read. Fresh content matches the shipped Tectonic PDF (the expected engine-dependent binary difference only).
- Lean: independently built the pinned Lean 4.19 / Mathlib project with `lake build`; exit 0, `Build completed successfully.` Direct `lake env lean -DwarningAsError=true Main.lean` also exited 0.
- Axioms: every principal theorem, including `matrix_mcCoy_iff`, reports only `[propext, Classical.choice, Quot.sound]`.
- Forbidden content: no `sorry`, `admit`, `native_decide`, extra axiom, `unsafe`, `implemented_by`, `extern`, or `skipKernelTC`.
- Auxiliary code: none documented; none is needed.

## Semantic audit
The Lean definitions encode the standard right and left McCoy properties over `A[X]`: nonzero zero-divisor polynomials must have a nonzero constant right/left annihilator, and `McCoy` is their conjunction. This is faithful to the source definition and does not depend on choosing only one handedness.

For `n = 1`, the explicit ring isomorphism `M_1(R) ≃ R` transfers both McCoy properties from the commutative ring `R`; the report also gives a correct classical minimal-degree proof. For `n ≥ 2`, the submission constructs explicit nonzero linear polynomials from matrix units. In the right case, `(1-E_jj)+E_ij X` annihilates `E_ji-E_ii X`, but any constant matrix `r` annihilating the first factor satisfies `r=(1-E_jj)r=0` and then `r=E_jj r=E_jiE_ij r=0`. The mirrored left construction is equally valid. Coefficient extraction proves the witnesses nonzero whenever `1≠0`; the argument works for arbitrary distinct indices, hence every `Fin n` with `n≥2`. Thus both one-sided properties genuinely fail and the examples are non-vacuous.

The final theorem states `McCoy (Matrix (Fin n) (Fin n) R) ↔ n = 1` for every nontrivial commutative `R` and `1≤n`, with the one-sided equivalences proved separately. The zero-ring degeneracy is explicitly disclosed and separately handled; under the standard nonzero matrix-ring convention, the correspondence is exact.

## Issues found
- Nonblocking scope flag: the theorem assumes `R≠0` (and `n≥1`). The report transparently explains that the zero ring is McCoy vacuously. This follows the usual nontrivial-matrix-ring convention; no intended nonzero case is omitted.

## Disposition
APPROVED — independent fresh rebuild and direct Lean check passed with only standard axioms; PDF and report agree; the theorem and both one-sided variants establish the intended matrix McCoy equivalence for all nontrivial commutative coefficient rings.
