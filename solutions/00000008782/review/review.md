# Solution Review — Conjecture 00000008782 (PR 438)

**Submission:** ziangni-sys — `ziangni-sys_submission_20261004061549`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-10-04

## Checklist results

- **Conjecture correspondence.** Attacks the unqualified Hutchinson variance-law conjunct exactly as stated, without importing a symmetry hypothesis. The concrete skew matrix gives actual variance 0 versus claimed value 4.
- **Repository structure.** PR head `c1e31ece...`, from clean base `4cc82278...`, adds only its correctly named submission folder. Base metadata has no prior solve.
- **LaTeX/PDF.** Read the full report and both shipped pages. Independently compiled twice with `pdflatex`; both exits 0. Ghostscript rendering succeeded.
- **Lean.** Independently linked the shared pinned Mathlib, ran `lake build` (exit 0, 2837 targets) and strict `Main.lean` replay (exit 0). All seven principal audits use only standard logical axioms.
- **Forbidden content.** No `sorry`, `admit`, `native_decide`, custom axiom, unsafe implementation, `extern`, `implemented_by`, or kernel-check bypass.
- **Auxiliary code.** None needed; probability and matrix calculations are exact Lean constructions.

## Semantic audit

For independent Rademacher `z`, the skew matrix `[[0,1],[-1,0]]` gives `zᵀAz=z₁z₂−z₂z₁=0` for every real vector. Therefore the estimator is constant zero, its expectation equals the zero trace, and its variance is zero. Its Frobenius squared norm is `1²+(-1)²=2` and both diagonal entries are zero, so the conjectured expression equals `4`.

Lean proves independence and Rademacher marginals on the actual four-outcome probability measure, then proves the universal quadratic-form identity and all numerical values. This concrete example is non-vacuous and falsifies the first conjunct of the official statement. The report correctly explains why symmetry is the missing hypothesis.

## Issues found

None blocking.

## Verdict rationale

The counterexample is mathematically decisive and faithfully formalized. Independent PDF, Lean, axiom, structure, and semantic checks pass.

## Disposition

**APPROVED**
