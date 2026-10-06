# Prove conjecture 00000000960: ℓ²(ℝ) has no Schauder basis, but every separable subspace has one

- **Forced non-separability.** A separable witness would be one of its own separable subspaces, so any witness must be non-separable.
- **Witness.** X = ℓ²(ℝ, 𝕜) for 𝕜 = ℝ or ℂ. It is not separable (uncountably many orthonormal vectors at mutual distance √2), so it has no Schauder basis; more strongly, no countably indexed (general) basis for any summation filter, and no sequence representing every vector as a convergent series.
- **Subspaces.** Every separable linear subspace V, closed or not, has a classical ℕ-indexed Schauder basis if infinite-dimensional (Gram–Schmidt on a dense sequence, expansion proved via the completion), and a finite orthonormal basis if finite-dimensional (stated convention: an ℕ-indexed basis cannot exist in finite dimension).
- **Non-vacuity.** An explicit closed, separable, infinite-dimensional subspace is exhibited.
- **Conventions.** "Schauder basis" is the classical sequence notion (Mathlib `SchauderBasis`); the convention allowing uncountable bases (under which ℓ²(ℝ) would have one) is not addressed. "Enflo direction" is context only: Enflo's space is separable, so it cannot witness this statement.
- **Main theorems.** `C960.conjecture960` (any `RCLike 𝕜`), `C960.conjecture960_real`.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 256 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture960/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000000960.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C960.conjecture960`, `C960.conjecture960_real`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000000960 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
