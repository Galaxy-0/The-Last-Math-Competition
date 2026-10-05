# Prove conjecture 00000005980: same singular spectrum, different eigenvector statistics via different polar decompositions

- **Explicit witnesses:** F(t) = R(t) S₀ R(t)ᵀ with S₀ = [[7,12],[0,−2]] and R(t) a rational rotation. Every F(t) is non-Hermitian, with eigenvalues {7, −2} and singular values {14, 1}.
- **Models:** A is the fair law on {F(0), F(1)}, and B is the fair law on {F(½), F(−½)}. Neither is a Dirac mass.
- **Same singular spectrum:** the laws of Mathlib's `LinearMap.singularValues` agree, computed exactly as (14, 1, 0, …). The eigenvalue laws also agree.
- **Different eigenvector statistics:** let the statistic be ‖proj onto the eigenvalue-7 eigenspace of e₀‖². Its law is ½δ₁ + ½δ₀ under A and δ_{9/25} under B.
- **Explicit pair:** F(0) ∈ supp A and F(½) ∈ supp B have the same singular values and the same spectrum. Their polar decompositions are unique, since positive square roots are unique (via CFC), and they differ in both the orthogonal factor and the positive factor.
- **Lean 4 / Mathlib v4.33.1:** `conjecture_5980 : ∃ A B X Y, Separation A B X Y`. The only axioms used are propext, Classical.choice and Quot.sound; there is no `sorry` and no `native_decide`.
- **Scope:** the claim is existential. No universality or asymptotic statement is made.
- **Credit:** the rotation family, eigenvector statistic and two-point ensembles adapt the accepted solution of 00000005960 (C0ldSmi1e, GPL-3.0).

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture5980/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000005980.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C5980.conjecture_5980`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000005980 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
