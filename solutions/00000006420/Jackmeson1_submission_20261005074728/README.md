# Prove conjecture 00000006420: two two-disk unions with equal isoperimetric deficit √2−1 but different Fraenkel asymmetry

This proves the conjecture with two explicit unions of two disjoint closed unit disks in ℝ²: `Enear = D(0,0) ∪ D(5/2,0)` and `Efar = D(0,0) ∪ D(10,0)`.
- **Definitions.** Perimeter P(E) = 𝓗¹(∂E). The deficit is δ(E) = P(E)/P(B_E) − 1 and the Fraenkel asymmetry is α(E) = inf_x |E Δ B(x, r_E)|/|E|, where |B_E| = |E|.
- **Same deficit.** Both sets have area 2π. The boundary of a disjoint union of closed sets is the union of the boundaries, so P = 2L, where L = 𝓗¹(unit circle) satisfies 0 < L < ∞ (the proofs show 2 ≤ L ≤ 2π). Scaling gives P(B_E) = √2·L, hence δ = √2 − 1 for both sets.
- **Different asymmetry.** No disk of radius √2 meets both far disks, so α(Efar) ≥ 1. The centre (2/5, 0) captures one disk plus a small disk inside the other, so α(Enear) ≤ 99/100.
- **Robustness.** Any deficit that is a function of (perimeter, area) agrees on the two sets, and any positive rescaling of α still separates them. Every translation-invariant perimeter that is additive on disjoint compact sets (as the De Giorgi perimeter is) also agrees.
- **Main theorems:** `separation`, `conjecture6420`, `normalisations`, `perimeter_axiomatic`.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture6420/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000006420.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C6420.separation`, `C6420.conjecture6420`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000006420 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
