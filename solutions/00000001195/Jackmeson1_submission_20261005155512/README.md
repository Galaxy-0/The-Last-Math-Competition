# Disprove conjecture 00000001195: ⟨p₍₂₎, p₍₂₎ * p₍₂₎⟩ = 4 = z₍₂₎², not z₍₂₎·δ

The conjecture claims ⟨p_λ, p_μ * p_ν⟩ = z_λ·δ for the Kronecker (inner) product * of symmetric functions. At λ = μ = ν = (2) the left side is 4 = z₍₂₎², while z₍₂₎ = 2, so z₍₂₎·δ ∈ {0, 2} for every 0/1 delta δ.
- **Model.** Degree-2 symmetric functions are modelled in `MvPolynomial (Fin 2) ℚ` (restriction isomorphism, N ≥ d), with Mathlib's `psumPart`, `hsymmPart`, `msymm`.
- **Hall inner product.** Any bilinear B with ⟨h_λ, m_μ⟩ = δ_{λμ} (λ, μ ⊢ 2).
- **Kronecker product.** Any bilinear K with ch(φ) * ch(ψ) = ch(φψ) for class functions on S₂, where ch(φ) = (1/2!) Σ_w φ(w) p_{ρ(w)} uses `Equiv.Perm.partition`.
- **Result.** Lean proves that such B and K exist and that for all of them ⟨p₍₂₎, p₍₂₎ * p₍₂₎⟩ = 4.
- **Not addressed.** The ordinary-product reading of * (where the identity is true), and non-0/1 readings of "δ with lexicographic counting".
- **Main theorem.** `C1195.conjecture_1195_false`.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 273 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture1195/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000001195.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C1195.conjecture_1195_false`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000001195 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
