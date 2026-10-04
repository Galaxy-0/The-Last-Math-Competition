# Solution Review — Conjecture 00000002305 (PR 478)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261004150934`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-04

## Verification

Full report/PDF and Lean source read. Fresh two-pass PDF compile, full Lean/Mathlib build, direct warning-as-error Lean check, and page rendering all exited 0. No forbidden proof shortcut occurs; all principal theorems use only standard foundational axioms. No auxiliary computation is needed.

## Counterexample

In the Frobenius group `C31⋊C5` realized by affine maps `x↦2^k x+a` on `Z/31`, the stabilizer of 0 is a maximal subgroup `H` of index 31. Conjugacy gives four classes of size 31 for nonzero k, one identity class, and six orbits/classes among the nonzero translations, for exactly 11 classes. Thus

`k(G)=11 < 31/2 = (1/2)[G:H]`.

Lean proves the group axioms, faithful affine action, order 155, index 31, maximality (`IsCoatom`), representative coverage, invariant class labels, exact class count 11, and negation of the universal all-groups/all-maximal-subgroups bound.

**Disposition: APPROVED.**
