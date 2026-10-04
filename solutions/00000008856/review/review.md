# Solution Review — Conjecture 00000008856 (PR 475)

**Submission:** ziangni-sys — `ziangni-sys_submission_20261004145233`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-04

## Verification

Full report/PDF and Lean source read. Fresh two-pass PDF compile, full Lean build, and direct warning-as-error Lean checking all exited 0. Only standard foundational axioms occur; no forbidden proof shortcut or auxiliary computation exists.

## Counterexample

Use the discrete nonexpansive semigroup `T(0)=id`, `T(n)(x)=|x|` for `n≥1` on ℝ. Its common fixed set is `[0,∞)`. Starting at `-1`, the orbit is `-1,1,1,...`; its Cesaro averages converge strongly and weakly to `1`. The unique nearest fixed point to `-1` is `0`, not `1`.

Lean proves the semigroup law, nonexpansiveness, fixed-set geometry, boundedness, average formula and limits, full functional weak convergence, projection, and uniqueness. Therefore the claimed projection identification is false. The averages themselves converge, so this is not an empty-fixed-set or unbounded-orbit artifact.

**Disposition: APPROVED.**
