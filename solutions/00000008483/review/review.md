# Solution Review — Conjecture 00000008483 (PR 477)

**Submission:** ziangni-sys — `ziangni-sys_submission_20261004150103`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-04

## Verification

Full report/PDF and Lean source read. Fresh two-pass PDF compile, full Mathlib build, direct warning-as-error check, and rendering all exited 0. No forbidden proof shortcut or auxiliary computation occurs; all principal theorems use only standard foundational axioms.

## Counterexample

Let `K={J}`, where `J=[[1,1],[0,1]]`. This family is compact. Its length-n products are exactly `J^n`; in the max norm, `||J^n||=n+1`, so the nth-root limit and joint spectral radius equal 1.

If `N` were an extremal norm, then `N(Jx)≤N(x)`. Iterating gives `N(J^n e2)≤N(e2)`, but `J^n e2=n e1+e2`. Norm subadditivity implies `nN(e1)≤2N(e2)` for every n, impossible because `N(e1)>0`. Hence no extremal norm exists; a fortiori no Barabanov norm exists. The example is reducible, exactly showing that compactness alone is insufficient.

Lean derives all products, exact operator norms, the joint-radius limit, and the universal definite-seminorm obstruction; no desired result is assumed.

**Disposition: APPROVED.**
