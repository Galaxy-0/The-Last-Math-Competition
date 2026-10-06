# Disprove conjecture 00000007789: the worst-case log-concave CLT distance d_n is not O(n^{−1/2})

- **Definition used.** Both languages set d_n = sup over isotropic log-concave X in ℝⁿ **and** unit directions θ of the Kolmogorov distance from Law⟨X, θ⟩ to N(0,1); the conjecture's clause about the "projecting directions" of the extremal simplex also points to a maximum over θ.
- **Witness.** X uniform on [−√3, √3]ⁿ: its density c^n·1_cube is log-concave, and it is isotropic (mean 0, covariance I, by independence of the product measure).
- **Bound.** With θ = e₁, ⟨X, θ⟩ is uniform on [−√3, √3], so the Kolmogorov distance is ≥ |F_U(√3) − Φ(√3)| = 1 − Φ(√3) ≈ 0.0416 > 0. Hence d_n ≥ 1 − Φ(√3) for every n ≥ 1 (`delta_le_worstDist`), and d_n is not O(n^{−1/2}).
- **Lean objects.** Mathlib's `cdf`, `gaussianReal 0 1`, `Measure.pi` and `IsBigO`; d_n is the `sSup` of admissible distances; log-concave = having a log-concave Lebesgue density; isotropic includes finite second moments; the unit sphere is Σθᵢ² = 1.
- **Not refuted.** A typical-direction (most θ) quantity as in Klartag's CLT (arXiv math/0605014, retrieved, context only); the later clauses (extremal simplex, convexity in the direction) are not addressed — refuting the first conjunct refutes the conjunction.
- **Main theorems.** `Conjecture7789.worstDist_not_isBigO`, `Conjecture7789.conjecture_false`.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 265 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture7789/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000007789.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `Conjecture7789.worstDist_not_isBigO`, `Conjecture7789.conjecture_false`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000007789 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
