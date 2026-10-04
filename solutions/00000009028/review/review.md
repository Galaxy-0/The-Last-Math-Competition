# Solution Review — Conjecture 00000009028 (PR 543)

**Submission:** C0ldSmi1e — `C0ldSmi1e_submission_20261004174358`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-10-04

## Checklist results

- **Conjecture correspondence.** Refutes the explicit even-determinant criterion for lattice evenness with two actual integral Euclidean lattices.
- **Repository structure.** PR head `6dd21d6e...`, from clean base `4cc82278...`, adds only its correctly named folder. Base metadata has no prior solve; copied conjecture and all hashes match.
- **LaTeX/PDF.** Read the full report and both shipped pages. Independently compiled twice; both exits 0. Ghostscript rendering succeeded.
- **Lean.** Independently linked shared Mathlib, built (exit 0, 2802 targets), and strictly replayed all four source modules plus Check; all five commands exited 0. All 47 audited declarations use only standard axioms.
- **Forbidden content.** No `sorry`, `admit`, `native_decide`, custom axiom, unsafe implementation, `extern`, `implemented_by`, or kernel-check bypass.
- **Auxiliary code.** None needed.

## Semantic audit

`A₂` is even but has Gram determinant 3, so even determinant is not necessary. The lattice with Gram matrix `diag(1,2)` has even determinant 2 but contains a norm-one vector, so it is not even; even determinant is not sufficient. Both are genuine positive-definite integral rank-two Euclidean lattices. Lean proves bases, inherited pairings, integrality, evenness/non-evenness, determinants, rank, full span, and discreteness from actual submodules and integer spans, then refutes both directions and the combined criterion.

## Issues found

None blocking.

## Verdict rationale

The two standard lattices decisively disprove determinant parity as an evenness criterion. Independent PDF, Lean, axiom, hash, structure, and semantic checks pass.

## Disposition

**APPROVED**
