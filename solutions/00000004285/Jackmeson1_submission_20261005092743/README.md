# Disprove conjecture 00000004285: a countable 2-free, not 3-free abelian group exists, so the least cardinality is not ℵ₁ at n = 2

The conjecture claims that the least cardinality of an n-free, not (n+1)-free group is ℵ_{n−1}, where n-free means every subset of size at most n lies in a free pure subgroup. At n = 2 this would be ℵ₁.
- **Reading.** Abelian groups, free = free abelian, pure = mA ∩ H ⊆ mH; subsets are finite with at most n elements, as the text's definition says.
- **Counterexample.** G = ℤ³ + Σ_k ℤ·(1,k,k²)/p_k ⊆ ℚ³, with p_k the k³-th prime. G is countable.
- **Not 3-free.** A pure H ∋ e₀, e₁, e₂ contains every w_k. Any map f : H → ℤ then has p_k | f(e₀) + k f(e₁) + k² f(e₂) for all k, which forces f(e₀) = 0, so H is not free.
- **2-free.** Two elements are orthogonal to some N ∈ ℤ³ \ 0. H = G ∩ N^⊥ is pure and has bounded denominators (only the finitely many k with p_k | N·(1,k,k²) contribute), so H is finitely generated and torsion-free, hence free.
- **Main theorems.** `C4285.not_minCardClaim`, `C4285.exists_countable_two_free_not_three_free`.
- **Scope.** Only the first part of the conjunction is formalized. Not refuted in Lean: a cardinal-indexed reading (κ-free, subsets of size < ℵ_n) and non-abelian readings. At n = 1 the claimed value ℵ₀ is not contradicted.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 400 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture4285/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000004285.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C4285.not_minCardClaim`, `C4285.exists_countable_two_free_not_three_free`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000004285 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
