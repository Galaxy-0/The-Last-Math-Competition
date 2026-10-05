# Prove conjecture 00000006630: two hard-core lattice gases with identical correlation inequalities but different equilibria

- **Reading:** a lattice-gas model is a hard-core (exclusion) gas: an exclusion graph on finitely many sites plus an activity `λ > 0`; its equilibrium is the Gibbs state `μ(η) = λ^|η| / Z` on allowed configurations, and its configuration count is the partition function `Z`.
- **Correlation inequalities:** the full sign profile `profile(B, C) = sign(⟨n_B n_C⟩ - ⟨n_B⟩⟨n_C⟩)` over all pairs of occupation monomials `n_B = [B ⊆ η]`.
- **Witnesses:** two adjacent sites (`Fin 2`, exclusion graph `⊤`) at activities `λ = 1` and `λ = 2`.
- **Identical inequalities:** the profile is the same for every `λ > 0` (`profile_K2_eq`); it is computed for all 16 pairs from `profile = sign(Z·W(B ∪ C) - W(B)·W(C))`.
- **Different equilibria:** `μ({0}) = 1/3` versus `2/5`.
- **Explicit violation:** both models violate the positive-correlation (FKG/Harris) inequality, `⟨n_0 n_1⟩ < ⟨n_0⟩⟨n_1⟩`.
- **Different configuration counting:** `Z = 3` versus `Z = 5`; with `q` internal particle states these are literal configuration counts (`card_internal_one/two`), and each equilibrium is the occupation marginal of the uniform distribution on those configurations (`gibbs_eq_count_one/two`).
- **Lean** (Mathlib v4.33.1): `conjecture6630 : ∃ M₁ M₂ : LatticeGas (Fin 2), profile M₁ = profile M₂ ∧ gibbs M₁ ≠ gibbs M₂ ∧ (violation in M₁) ∧ (violation in M₂) ∧ Z M₁ = 3 ∧ Z M₂ = 5 ∧ …`. Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
- **Scope:** hard-core, finite-volume, grand-canonical reading; soft interactions and infinite-volume Gibbs measures are not treated.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture6630/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000006630.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `Submission00000006630.conjecture6630`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000006630 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
