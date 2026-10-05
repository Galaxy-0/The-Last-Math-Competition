# Disprove conjecture 00000006120: identical noise stability forces identical degree and low-degree Fourier weights

The conjecture asks for two Boolean functions with identical noise stability but different spectral distributions. The separation is to be realized by an explicit perturbation with the same stability but different low-degree weights. The last clause can never hold.
- **Definitions (O'Donnell).** `Stab_ρ[f] = E[f(x)f(y)]`, where `x` is uniform and `y ~ N_ρ(x)`. This is defined from the actual noise kernel `∏ᵢ [(1+ρ)/2 if yᵢ = xᵢ, else (1-ρ)/2]`, which is proved to sum to 1. The degree weight is `W^k[f] = ∑_{|S|=k} f̂(S)²` and the low-degree weight is `W^{≤k}[f] = ∑_{|S|≤k} f̂(S)²`.
- **Key fact.** `Stab_ρ[f] = ∑_S ρ^{|S|} f̂(S)² = ∑_k W^k[f] ρ^k`, proved from the probabilistic definition (`stab_eq_fourier`, `stab_eq_weights`). So `ρ ↦ Stab_ρ[f]` is a polynomial whose coefficients are exactly the degree weights.
- **Consequence.** If two functions (of any arities) have the same stability at infinitely many `ρ`, then they have the same `W^k` and the same `W^{≤k}` for every `k` (`weight_eq_of_stab_eq`, `lowWeight_eq_of_stab_eq`). This uses Mathlib's `Polynomial.eq_of_infinite_eval_eq`.
- **Disproof.** No pair with equal stability on `[0,1]` has a differing `W^k` or `W^{≤k}` (`no_realizing_pair`). Hence `conjecture6120_false : ¬ Statement`. The realizing pair may be the separating pair or a different one. Booleanity is not used, so the result also holds for `{0,1}`-valued functions.
- **Non-vacuity.** The dictators `x₀` and `x₁` have identical stability for every `ρ` and different spectral distributions (`first_clauses_satisfiable`). Only the realizing clause fails.
- **Not refuted.** (i) Reading "low-degree weights" as individual coefficients `f̂(S)²` on low-degree sets; under this reading the dictators satisfy the clause. (ii) Reading "same stability" as equality at a single `ρ`.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 274 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture6120/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000006120.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `Conjecture6120.conjecture6120_false`, `Conjecture6120.no_realizing_pair`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000006120 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
