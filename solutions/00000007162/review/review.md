# Solution Review — Conjecture 00000007162 (PR 507)

**Submission:** ziangni-sys — `ziangni-sys_submission_20261004160907`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-10-04

## Checklist results

- **Conjecture correspondence.** Refutes the stated normality-of-critical-points claim on the unrestricted matrix domain using a nonconstant convex eigenvalue-dependent function and a nonnormal Jordan critical point.
- **Repository structure.** PR head `b88d956a...`, from clean base `4cc82278...`, adds only its correctly named folder. Base metadata has no prior solve.
- **LaTeX/PDF.** Read the full report and both pages. Independently compiled twice; both exits 0. Ghostscript rendering succeeded.
- **Lean.** Independently linked shared Mathlib, built (exit 0, 2032 targets), and strictly replayed Main (exit 0). All eight audited theorems use only standard axioms.
- **Forbidden content.** No `sorry`, `admit`, `native_decide`, custom axiom, unsafe implementation, `extern`, `implemented_by`, or kernel-check bypass.
- **Auxiliary code.** None needed.

## Semantic audit

The function `(tr M)²` is determined by the characteristic polynomial, hence by eigenvalues with multiplicity, and is similarity invariant. The identity `a f(M)+b f(N)-f(aM+bN)=ab(tr M-tr N)²` proves global convexity. Its derivative is `2 tr(M) tr(H)`, so the trace-zero Jordan nilpotent is Fréchet critical. That matrix fails `MMᵀ=MᵀM`. Thus a convex spectral function has a nonnormal critical point, disproving the official claim as written.

## Issues found

None blocking.

## Verdict rationale

The explicit functional and derivative calculation are correct and fully formalized. Independent PDF, Lean, axiom, structure, and semantic checks pass.

## Disposition

**APPROVED**
