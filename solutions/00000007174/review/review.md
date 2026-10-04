# Solution Review — Conjecture 00000007174 (PR 509)

**Submission:** ziangni-sys — `ziangni-sys_submission_20261004164100`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-10-04

## Checklist results

- **Conjecture correspondence.** Directly refutes the claimed antisymmetric-norm lower bound for spectral condition number using a normal invertible scaled rotation.
- **Repository structure.** PR head `c8ad5635...`, from clean base `4cc82278...`, adds only its correctly named folder. Base metadata has no prior solve.
- **LaTeX/PDF.** Read the full report and shipped page. Independently compiled twice; both exits 0. Ghostscript rendering succeeded.
- **Lean.** Independently linked shared Mathlib, built (exit 0, 2799 targets), and strictly replayed Main (exit 0). All six audited theorems use only standard axioms.
- **Forbidden content.** No `sorry`, `admit`, `native_decide`, custom axiom, unsafe implementation, `extern`, `implemented_by`, or kernel-check bypass.
- **Auxiliary code.** None needed.

## Semantic audit

The scaled rotation has operator norm 2 and inverse norm 1/2, so spectral condition number is 1. It is normal and equals its normalized antisymmetric part, whose norm is 2. Therefore the asserted lower bound fails. Its eigenvalues ±2i have equal moduli, so the eigenvalue-ratio interpretation also fails. Lean proves all norms, inverses, adjoint, normality, antisymmetric part, eigenvalues, and ratios from actual Mathlib objects.

## Issues found

None blocking.

## Verdict rationale

The numerical and functional-analytic counterexample is decisive and fully formalized. Independent PDF, Lean, axiom, structure, and semantic checks pass.

## Disposition

**APPROVED**
