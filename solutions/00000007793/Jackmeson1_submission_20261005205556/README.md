# Disprove conjecture 00000007793: Var|X−Y|/Var|X| is not 2 − 2/√3 + O(1/n) for uniform points in the n-ball

- **Claim refuted.** The two-point distance variance ratio for independent uniform points in the n-ball is 2 − 2/√3 + O(1/n) ≈ 0.845 (the first conjunct; n is the dimension).
- **Bound.** Var|X−Y|/Var|X| ≥ (n+1)²/(4(n+2)) ≥ n/8 for every n ≥ 1, so the ratio tends to +∞ and has no finite limit (`ratio_ge`, `ratio_tendsto_atTop`, `no_finite_limit`).
- **Var|X|.** = n/((n+1)²(n+2)), from the radial moments E|X|^k = n/(n+k) via polar coordinates (`integral_fun_norm_addHaar`).
- **Var|X−Y|.** The symmetry Y ↦ −Y and |X+Y|² − |X−Y|² = 4⟨X,Y⟩ give Var|X−Y| ≥ E⟨X,Y⟩²/4, and E⟨X,Y⟩² = Σᵢⱼ (E XᵢXⱼ)² ≥ (E|X|²)²/n = n/(n+2)².
- **Models.** `not_conjecture` uses the product measure of `ProbabilityTheory.cond volume (ball 0 1)` on `EuclideanSpace ℝ (Fin n)`; `not_conjecture_rv` covers any independent X_n, Y_n uniform on balls of any radius r_n > 0 (unit-ball and isotropic normalizations). Variance is Mathlib's `ProbabilityTheory.variance`.
- **Not addressed.** The −1/(3√3) correction coefficient and the coupling clause; refuting the first conjunct refutes the conjunction.
- **Main theorems.** `C7793.not_conjecture`, `C7793.not_conjecture_rv`.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 361 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture7793/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000007793.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C7793.not_conjecture`, `C7793.not_conjecture_rv`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000007793 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
