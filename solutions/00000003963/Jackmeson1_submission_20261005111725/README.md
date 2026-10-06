# Disprove conjecture 00000003963: the algebraic connectivity of hypercube layers is not Θ(log n / n²)

- **Johnson reading.** The layer graph is J(n, ℓ). Lean proves λ₂(L(J(n,ℓ))) ≥ n for every n and every 1 ≤ ℓ ≤ n−1 (`algConn_johnson_ge`), so even the minimum over layers is not O(log n / n²) (`conjecture_3963_false`).
- **λ₂ in Lean.** Mathlib's `eigenvalues₀` (sorted in decreasing order) at index card−2 of `lapMatrix`, i.e. Fiedler's second smallest Laplacian eigenvalue with multiplicity. The step from the quadratic form to the eigenvalue is proved by hand from the orthonormal eigenbasis (`lambda2_ge`).
- **Key bound.** xᵀLx ≥ n‖x‖² for x orthogonal to the constants, via up/down operators on subsets, the commutation identity DU − UD = (n−2k)I, Cauchy–Schwarz and induction on the layer (`johnson_quad`).
- **Normalized Laplacian.** J is regular, so λ₂ ≥ 4/n at ℓ = n/2, also not O(log n / n²) (`normConn_johnson_ge`).
- **Literal reading.** The subgraph of Q_n induced on a layer has no edges, so λ₂ = 0, not Ω(log n / n²) (`algConn_inducedLayer`).
- **Difference from the closed PR #287.** The graphs, Laplacians and eigenvalues are defined in Lean, and the statements cover all even n, not finitely many.
- **Scope.** Under the Johnson reading the "minimum at ℓ = n/2" clause is not refuted (all non-trivial layers have λ₂ ≥ n); the conjecture fails through its order clause.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 564 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture3963/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000003963.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C3963.conjecture_3963_false`, `C3963.algConn_johnson_ge`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000003963 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
