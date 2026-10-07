# Disprove conjecture 00000007783: the isotropic cube has thin-shell deviation at least 1/√15 in every dimension, so σ_n is not O(n^{-1/4})

- **Reading.** σ_n = sup over isotropic convex bodies K ⊂ ℝⁿ (compact, convex, nonempty interior; X uniform on K with E X = 0, E XXᵀ = I) of √Var|X|.
- **Witness.** The cube [−√3, √3]ⁿ is an isotropic convex body (Fubini: E X_i = 0, E X_iX_j = δ_ij).
- **Bound.** Var|X|² = 4n/5 there, and since |X| ≤ √(3n), Var|X| ≥ Var|X|²/(12n) = 1/15 for every n ≥ 1.
- **Consequence.** No C, N give sd(K) ≤ C·n^{−1/4} for all isotropic K in all dimensions n ≥ N: the upper bound in σ_n = Θ(n^{−1/4}) fails, and so does the upper half of the interpolation clause. The same holds in the volume-one convention (cube [−1/2,1/2]ⁿ, sd ≥ 1/√180).
- **Main theorems.** `C7783.not_thinShell_le_rpow`, `C7783.not_sigma_le_rpow`, `C7783.not_thinShell_le_rpow_volOne`.
- **Scope.** Not assessed: the ball/simplex values, strict monotonicity, and the interpolation law. The filter's original n = 1 ball-value counterexample was degenerate and is not used.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 340 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture7783/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000007783.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C7783.not_thinShell_le_rpow`, `C7783.not_sigma_le_rpow`, `C7783.not_thinShell_le_rpow_volOne`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000007783 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
