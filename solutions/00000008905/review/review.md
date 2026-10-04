# Solution Review — Conjecture 00000008905 (PR 542)

**Submission:** ziangni-sys — `ziangni-sys_submission_20261004192500`
**Reviewer:** independent competition reviewer (structure + build + semantic audit)
**Date:** 2026-10-04

## Checklist results
- Conjecture read: yes — the statement claims reconstruction of homomorphism counts from adjacency eigenvalues.
- Path policy: pass — only the submitter's own directory was added; clean-base metadata is unsolved/undisproved.
- LaTeX: independent `latexmk -pdf` build exited 0; both pages extracted/rendered and read. Content matches the shipped Tectonic PDF.
- Lean: fresh Mathlib-pinned project built with `lake build`; exit 0. Direct `lake env lean -DwarningAsError=true Main.lean` exited 0 without warnings.
- Axioms: all ten principal theorems use only `[propext, Classical.choice, Quot.sound]`.
- Forbidden content: no `sorry`, `admit`, `native_decide`, extra axiom, `unsafe`, `implemented_by`, `extern`, or `skipKernelTC`.
- Auxiliary code: none required. I independently recomputed characteristic polynomials, spectra, degree lists, and exhaustively enumerated all path homomorphisms.

## Semantic audit
The six-vertex graphs `K_{1,4}⊔K_1` and `C_4⊔2K_1` both have adjacency spectrum `{2,-2,0,0,0,0}`. For the three-vertex path, homomorphisms are counted by `Σ_v deg(v)^2`. The star has degree list `(4,1,1,1,1,0)`, giving 20; the cycle has `(2,2,2,2,0,0)`, giving 16. Thus one common eigenvalue multiset must reconstruct two different counts, which is impossible.

Lean constructs the actual simple graphs and adjacency matrices, proves cospectrality through an explicit invertible intertwiner and determinant argument, transfers equality to complex root multisets, establishes an equivalence to actual `SimpleGraph.Hom`, and kernel-checks the counts 20 and 16. The counterexample is finite, explicit, and non-vacuous. It refutes unrestricted graph-homomorphism reconstruction without denying the standard fact that spectra determine closed-walk counts.

## Issues found
- none blocking.

## Disposition
APPROVED — independent LaTeX/Lean reproduction and separate exact finite checks passed with only standard axioms; the cospectral pair has unequal homomorphism counts, decisively refuting spectral reconstruction.
