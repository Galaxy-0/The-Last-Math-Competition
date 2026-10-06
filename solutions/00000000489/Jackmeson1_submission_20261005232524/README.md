# Disprove conjecture 00000000489: S₃(n) = Σ_λ f_λ³/n! is not Θ(√(n!)·n^{1/4})

- **Key inequality.** For pairwise non-isomorphic irreducible complex representations of a finite group G, Σ (dim V_i)² ≤ |G|: via character orthonormality (`FDRep.char_orthonormal`) applied to Φ = Σ d_i χ_i, giving |G|·D = Σ_g |Φ(g)|² ≥ Φ(1)² = D², with χ(g⁻¹) = conj χ(g) proved through the invariant positive-definite matrix Σ A_hᴴA_h.
- **Bound.** Hence every f_λ ≤ √(n!) and S₃(n) = Σ f_λ³/n! ≤ max f_λ ≤ √(n!) for every n, so S₃(n)/(√(n!)·n^{1/4}) ≤ n^{−1/4} → 0.
- **Refutation.** This refutes the Θ lower bound, the limit constant 2^{1/4}π^{−1/2}, and S₃/√(n!) ~ 2^{1/4}π^{−1/2}·n^{1/4} (Mathlib `=o[atTop]`, `=Θ[atTop]`, `~[atTop]`). Numerically, at n = 30 the ratio is ≈ 0.018 versus the claimed 0.671.
- **Formalization.** `conjecture489_false` quantifies over every partition-labelled family of simple, pairwise non-isomorphic `FDRep ℂ (Equiv.Perm (Fin n))`; the true family of irreducibles of S_n (classical classification, quoted from a retrieved source, not constructed in Lean) is one such family. If f_λ is read as the number of standard Young tableaux, the theorem applies through the classical identity #SYT = dim (not formalized).
- **Not addressed.** "3-thread counting of the limit shape" (no formal meaning) and the garbled Chinese prefix beyond its explicit Θ claim; √n! is read as √(n!).
- **Main theorem.** `C489.conjecture489_false`.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 264 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture489/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000000489.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C489.conjecture489_false`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000000489 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
