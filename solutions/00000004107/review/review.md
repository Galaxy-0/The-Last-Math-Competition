# Solution Review — Conjecture 00000004107 (PR 432)

**Submission:** C0ldSmi1e — `C0ldSmi1e_submission_20261004090205`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-10-04

## Checklist results

- **Conjecture correspondence.** Read `conjectures/00000004107.md` in full. The official bilingual conjecture states that subspace-arrangement characteristic-polynomial coefficients are always strictly alternating and that the sign pattern is determined by the dimension spectrum. The submission attacks and refutes the universal strict-alternation conjunct with an explicit valid subspace arrangement; a false conjunct disproves the whole conjunction. The submission's `conjecture.md` is byte-identical to the official statement.
- **Repository structure.** PR head `5eb86f4c8e1b4f8f02e791aaa4c74474b939fba9`, from clean base `4cc82278...`, adds only its correctly named folder under `solutions/00000004107/`. No root, metadata, official conjecture, or unrelated review files are changed. Base metadata has no solver and marks the conjecture neither proven nor disproven.
- **LaTeX/PDF.** Read the complete report and both shipped PDF pages. Independently rebuilt `main.tex` twice with `pdflatex`; both passes exited 0 with no errors. The fresh and shipped two-page PDFs have equivalent extracted content. Ghostscript rendered the shipped PDF successfully.
- **Lean.** Independently rebuilt the pinned Lean 4.19.0 / Mathlib `c44e0c8...` project after official cache preseeding: `lake build` exit 0. Replayed all five Lean files with `lake env lean -DwarningAsError=true`; all five exited 0, with no warnings or errors from the proof sources. `Check.lean` output is byte-identical to shipped axiom evidence and audits 47 theorems; every dependency list is a subset of `[propext, Classical.choice, Quot.sound]`.
- **Forbidden content.** No `sorry`, `admit`, `native_decide`, extra axiom, unsafe definition, `implemented_by`, `extern`, custom proof bypass, or `skipKernelTC`. Kernel-checked `decide`/`fin_cases` are used only for the finite four-subset classification.
- **Auxiliary code.** None is needed; this is an exact Lean computation from actual geometric objects, not a sampling program. All submission hashes in `SHA256SUMS.json` independently match.

## Semantic audit

The counterexample is the real arrangement in `ℝ³` consisting of

\[
U=\{(a,b,0):a,b\in\mathbb R\},\qquad W=\{(0,0,c):c\in\mathbb R\}.
\]

These are distinct proper nonzero subspaces, neither contained in the other, with intersection `{0}`. Thus the complete intersection poset is
