# Solution Review — Conjecture 00000008241 (PR 437)

**Submission:** ziangni-sys — `ziangni-sys_submission_20261004061902`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-10-04

## Checklist results

- **Conjecture correspondence.** Attacks the official coalition-gain subadditivity conjunct: coalition VCG gain should be at most coalition size times the single-agent gain. The actual two-agent VCG auction gives coalition gain 1 while each individual maximum gain is 0.
- **Repository structure.** PR head `fa22974a...`, from clean base `4cc82278...`, adds only its correctly named folder. Base metadata has no prior solve.
- **LaTeX/PDF.** Read the complete report and both shipped pages. Independently compiled twice with `pdflatex`, both exits 0; Ghostscript rendering succeeded.
- **Lean.** Independently linked shared pinned Mathlib, ran `lake build` (exit 0, 907 targets) and strict `Main.lean` replay (exit 0). All five principal audits use only standard axioms.
- **Forbidden content.** No `sorry`, `admit`, `native_decide`, custom axiom, unsafe implementation, `extern`, `implemented_by`, or `skipKernelTC`.
- **Auxiliary code.** None needed; exact auction arithmetic and universal unilateral-report coverage are in Lean.

## Semantic audit

For true values `(2,1)`, truthful VCG utilities are `(1,0)`. Any unilateral nonnegative deviation gives the deviator gain at most 0, with truth attaining 0. If both agents report `(2,0)`, agent 0 wins for free, giving utilities `(2,0)` and total coalition gain 1. Therefore `1 > 2·0`, decisively violating the claimed bound.

Lean uses all three feasible allocations, proves reported-welfare maximization and actual Clarke-pivot payments, quantifies over every nonnegative unilateral report including ties, computes the two-agent coalition gain by a finite sum, and proves its cardinality. The counterexample is non-vacuous and refutes a universal conjunct of the official statement.

## Issues found

None blocking.

## Verdict rationale

The example is a genuine VCG mechanism and provides a strict, fully formal counterexample to the coalition-gain bound. Independent PDF, Lean, axiom, structure, and semantic checks pass.

## Disposition

**APPROVED**
