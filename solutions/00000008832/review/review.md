# Solution Review — Conjecture 00000008832 (PR 496)

**Submission:** ziangni-sys — `ziangni-sys_submission_20261004154010`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-04

## Checklist results

- **Eligibility and scope.** The three-dot diff from clean base `4cc82278` adds only the correctly named personal submission folder. Base metadata marks conjecture 00000008832 unsolved. The report accurately quotes and addresses the unconditional convergence assertion in both official languages.
- **LaTeX and PDF.** I read the complete two-page report and every submitted source/config file. Fresh `latexmk -pdf` compilation succeeded (exit 0; 2 pages). I extracted and compared shipped/fresh text and rendered both fresh pages with Ghostscript. No auxiliary numerical program is used or required.
- **Lean.** Using the official shared pinned Mathlib tree, `lake build` completed successfully. Direct `lake env lean -DwarningAsError=true Main.lean` exited 0. Nine central axiom audits report exactly `[propext, Classical.choice, Quot.sound]`.
- **Forbidden-content scan.** No `sorry`, `admit`, custom `axiom`, `native_decide`, `unsafe`, `implemented_by`, `extern`, `skipKernelTC`, or trust override occurs. Only legitimate `#print axioms` audits contain “axiom”.

## Semantic audit

The official first assertion says FBF “always converges” under joint Lipschitz monotonicity, with no solution-existence hypothesis. The submission uses the standard forward-backward-forward recurrence

`v=x-γB(x)`, `y=J_{γA}(v)`, `x⁺=y-γ(B(y)-B(x))`

on the real Hilbert space. Take `A(x)={0}` and `B(x)=1`.

Both graphs are horizontal constant graphs and hence maximal monotone. The formal maximality proof compares any putative extension point `(p,q)` with `(p±1,c)`, forcing `q=c`. The single-valued representatives are constant, therefore `0`-Lipschitz and in particular `1`-Lipschitz. Thus the joint Lipschitz-monotonicity hypotheses are met.

For `A=0`, the resolvent equation `v=y+γa` with `a∈A(y)={0}` has the exact unique solution `y=v`. Therefore the first forward stage gives `v=x-γ`; the backward stage gives `y=v`; and the final forward correction is zero because `B` is constant. Hence every FBF update is exactly `x⁺=x-γ`. Lean proves the genuine resolvent equation, all three stages, and the resulting update.

Choosing `γ=1/2` satisfies `0<γ<1/L` for `L=1`, so this is not a step-size-domain violation. For every initial `x`, the orbit is `x_n=x_0-n/2`. A convergent sequence must have consecutive differences tending to zero, but here `x_{n+1}-x_n=-1/2` identically. Thus there is no strong limit. Lean's weak convergence predicate quantifies over every continuous linear functional; applying the identity functional reduces weak convergence to strong convergence, so there is no weak limit either.

The inclusion is `0∈A(x)+B(x)={1}`, which has no solution. This is exactly the missing hypothesis: Lipschitz monotonicity alone does not imply zero existence, and an orbit cannot converge to a solution when none exists. The submission transparently distinguishes this literal unconditional disproof from standard FBF theorems that add an existence assumption; it does not claim to refute those conditional theorems or the separate adaptive-backtracking clause.

## Verdict rationale

The counterexample satisfies the stated operator hypotheses and a safe standard step, implements the genuine FBF stages, and proves all-start/all-iterate weak nonconvergence. It decisively refutes the conjecture's unconditional “always converges” clause. Builds, direct replay, axiom audits, PDF checks, and scans all pass.

## Disposition

APPROVED — ready for merge (PR 496). No merge action was taken by this reviewer.
