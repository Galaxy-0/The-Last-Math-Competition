# Solution Review — Conjecture 00000000428 (PR 532)

**Submission:** C0ldSmi1e — `C0ldSmi1e_submission_20261004172029`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-10-04

## Checklist results

- **Conjecture correspondence.** Refutes the exact displayed uniform Durfee-mean asymptotic in both language versions.
- **Repository structure.** PR head `a1e75358...`, from clean base `4cc82278...`, adds only its correctly named folder. Base metadata has no prior solve. The copied conjecture is byte-identical and all submitted hashes match.
- **LaTeX/PDF.** Read the full report and both shipped pages. Independently compiled twice; both exits 0. Ghostscript rendering succeeded.
- **Lean.** Independently linked shared Mathlib, built (exit 0, 2844 targets), and strictly replayed all four source modules plus Check; all five commands exited 0. All 38 audited declarations use only standard axioms.
- **Forbidden content.** No `sorry`, `admit`, `native_decide`, custom axiom, unsafe implementation, `extern`, `implemented_by`, or kernel-check bypass.
- **Auxiliary code.** None needed; the all-partition bound and asymptotic contradiction are formal Lean proofs.

## Semantic audit

Every Durfee square of side `d` occupies `d²` cells inside a partition of `n`, so `d≤√n`; averaging gives `E_n≤√n`. The proposed term `(√(6n)/π)log(√(6n)/π)` eventually exceeds `2√n`, so its excess over `E_n` tends to infinity. Therefore no fixed real constant plus an additive `o(1)` term can satisfy the claimed expansion. Lean formalizes actual partitions, Ferrers diagrams, uniform measure, integral mean, square-root bound, and exact asymptotic negation.

## Issues found

None blocking.

## Verdict rationale

The deterministic area bound makes the `√n log n` leading term impossible, decisively disproving the conjecture. Independent PDF, Lean, axiom, hash, structure, and semantic checks pass.

## Disposition

**APPROVED**
