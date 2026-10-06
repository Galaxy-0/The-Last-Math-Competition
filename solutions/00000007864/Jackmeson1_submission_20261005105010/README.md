# Disprove conjecture 00000007864: the men-optimal stable matching is exactly uniform, so the entropy deficit constant is 1, not π²/6

- **Model.** n men and n women, all 2n strict preference lists independent and uniform; σ_m is the men-optimal stable matching; H is the Shannon entropy (natural log) of the law of σ_m; D_n = n log n − H(σ_m).
- **Gale–Shapley in Lean.** Existence and uniqueness of the men-optimal stable matching are proved from scratch (`exists_menOptimal`, `menOptimal_unique`).
- **Symmetry.** Relabelling the women is a bijection on profiles that commutes with the men-optimal map (`menOpt_relabel`), so the law of σ_m is exactly uniform on S_n (`law_menOpt_eq_uniform`, stated with Mathlib's `PMF.uniformOfFintype` and `PMF.map`).
- **Entropy.** H(σ_m) = log n! (`entropy_menOpt`), and n − 1 − ½ log n ≤ D_n ≤ n (`deficit_ge` via Mathlib's Stirling sequence, `deficit_le`).
- **Main theorem.** `C7864.conjecture_7864_false`: D_n/n ≤ 1 < π²/6 for every n ≥ 1, D_n/n → 1, and D_n/n does not tend to π²/6. `bits_version`: with base-2 logs the limit is 1/ln 2, also not π²/6.
- **Scope.** The clause D_n = Θ(n) is true; the LIS/Tracy–Widom clause is not addressed. The conjunction is refuted through its c* = π²/6 clause.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 390 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture7864/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000007864.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C7864.conjecture_7864_false`, `C7864.law_menOpt_eq_uniform`, `C7864.exists_menOptimal`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000007864 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
