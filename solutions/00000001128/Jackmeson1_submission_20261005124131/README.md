# Disprove conjecture 00000001128: M(w, ℓ(w)) is not divisible by min(j, ℓ, ⌈ℓ/2⌉)!

- **Witness.** For w = 321 = w₀ ∈ S₃, 𝔖₃₂₁ = x₁²x₂ (the base case of the divided-difference recursion), so M(321,3) = 1, while the formula requires min(3,3,2)!·C = 2C; 1 = 2C has no integer solution.
- **321-avoiding witness.** The same contradiction holds for w = 4123 ∈ S₄, where 𝔖₄₁₂₃ = ∂₃∂₂∂₃ x^δ = x₁³ and ℓ = 3, so the reading restricted to 321-avoiding permutations is also refuted.
- **Objects in Lean.** ∂ᵢ is the exact quotient (P − sᵢP)/(xᵢ − xᵢ₊₁), with divisibility proved for every P. Schubert polynomials are defined by the Lascoux–Schützenberger characterization (𝔖 of w₀, ∂ᵢ on descents, 0 otherwise), and the explicit S₃ and S₄ families are proved to satisfy it.
- **Scope.** Stability of Schubert polynomials from Sₙ to Sₙ₊₁ is not formalized; each witness lives in a fixed Sₙ.
- **Main theorems.** `C1128.disproof`, `C1128.disproof_321_avoiding`.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 347 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

**Previous submission and its error (README rule 2).** Two submissions by orionsheep for this conjecture were closed without merging. PR #161 formalized the wrong object. PR #201 had the right mathematics (𝔖₃₂₁ = x₁²x₂, M(321,3) = 1 against the factor 2! = 2), but the reviewer rejected it because it "hardcodes the polynomial as an opaque monomial list [(2,1,0,1)] with no divided-difference construction and no Lean proof that this list IS the Schubert polynomial of 321". The reviewer asked for a version "deriving 𝔖₃₂₁ from w₀ by divided differences". This submission defines the divided difference ∂_i in Lean as the exact quotient (P − s_iP)/(x_i − x_{i+1}) in ℤ[x], proving divisibility for every P. It defines Schubert polynomials by the Lascoux–Schützenberger characterization: 𝔖_{w₀} = x^δ, ∂_i𝔖_w = 𝔖_{ws_i} on descents, and 0 otherwise. It proves that the explicit S₃ and S₄ families satisfy this characterization. It then refutes the formula at w = 321, where 321 = w₀, and at the 321-avoiding w = 4123 ∈ S₄, where 𝔖₄₁₂₃ = ∂₃∂₂∂₃ x^δ = x₁³. Lean indexes variables and positions from 0, so there this reads ∂₂∂₁∂₂ x^δ = x₀³.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture1128/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000001128.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C1128.disproof`, `C1128.disproof_321_avoiding`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000001128 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
