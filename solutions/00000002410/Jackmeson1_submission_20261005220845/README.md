# Prove conjecture 00000002410: the middle-half Cantor measure (base-4 digits {0,3}) is not Rajchman

- **Witness.** K = {Σ dᵢ4^{−(i+1)} : dᵢ ∈ {0,3}} and μ = the law of i.i.d. fair digits (pushforward of `Measure.infinitePi` of the fair coin), a probability measure with μ(K) = 1.
- **Homogeneous Cantor set.** K is compact, homeomorphic to {0,1}^ℕ, and K = K/4 ∪ (K/4 + 3/4) (self-similar with the same ratio 1/4 for both maps).
- **Dimension.** dim_H K = 1/2: the upper bound from covers by 2ⁿ intervals of length 4⁻ⁿ (H^{1/2}(K) ≤ 1), the lower bound from a 1/2-Hölder map of K onto [0,1] (base 4 to base 2), using Mathlib's `Real.ofDigits`.
- **Non-decay.** Re μ̂(4ⁿ) ≥ 1/8 for every n (4ⁿx is x shifted by n digits mod 1; cos 2πy ≥ 0 on K and ≥ 1/2 on a set of mass 1/4), so μ̂ does not tend to 0 as |ξ| → ∞, nor along the integers.
- **×4, not ×2.** μ is invariant under x ↦ 4x mod 1 but not under x ↦ 2x mod 1 (the interval (1/4, 3/4) has μ-mass 0 but pushforward mass ≥ 1/4); "blocking" is formalized as this invariance property.
- **Scope.** Classical example (Wikipedia "Rajchman measure" and "Cantor space" retrieved for definitions); uniqueness of the self-similar set and supp μ = K are not proved.
- **Main theorem.** `C2410.main`.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 477 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture2410/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000002410.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C2410.main`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000002410 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
