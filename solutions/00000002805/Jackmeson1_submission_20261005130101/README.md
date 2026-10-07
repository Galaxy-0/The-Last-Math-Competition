# Disprove conjecture 00000002805: the Schilder rate does not vanish on the Cameron–Martin unit ball

- **Witness.** The path ω₀(t) = t·e₀/(2√T) in C₀([0,T]; ℝ^d) has ‖ω₀‖²_H = 1/4, so it lies in the open and in the closed Cameron–Martin unit ball. Its Schilder rate is I(ω₀) = ½·¼ = 1/8 ≠ 0.
- **Consequence.** "I(ω) = 0 iff ω lies in the Cameron–Martin unit ball" fails for every d ≥ 1 and T > 0; the true zero set of I is {0}.
- **Objects in Lean.** Path space C₀; Cameron–Martin space (absolutely continuous via Mathlib's `AbsolutelyContinuousOnInterval`, ω(0) = 0, derivative in L²); the Cameron–Martin norm; both unit balls; I(ω) = ½∫₀ᵀ‖ω̇‖², or +∞ off the absolutely continuous paths.
- **Scope.** Only the first clause ("Cameron–Martin rigidity") is refuted; the chi-square clause about the sphere is not interpreted.
- **Main theorems.** `C2805.schilder_rigidity_false`, `C2805.schilder_rigidity_false_open`.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 148 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

**Previous submission and its error (README rule 2).** PR #277 by orionsheep gave the counterexample ω(t) = t/2 (Cameron–Martin norm 1/2, Schilder rate 1/8) but was closed without merging. The reviewer's reason: "conjecture_refuted is entirely vacuous ℕ trivia (∀c>0, 0<c·c, 1 ≤ 2, 1 ≠ 0, 2 = 1·2, 1 ≠ 2); the Schilder rate, Cameron–Martin space, sphere, and chi-square law never appear in Lean." This submission defines in Lean the path space C₀([0,T]; ℝ^d), the Cameron–Martin space (absolutely continuous paths with ω(0) = 0 and derivative in L²), the Cameron–Martin norm, the closed and open unit balls, and Schilder's rate function I(ω) = ½∫₀ᵀ‖ω̇‖² (+∞ off the absolutely continuous paths). For every d ≥ 1 and T > 0 it proves that ω₀(t) = t·e₀/(2√T) lies in both balls (‖ω₀‖²_H = 1/4) while I(ω₀) = 1/8 ≠ 0, so "I(ω) = 0 iff ω is in the unit ball" fails. Unlike PR #277, it makes no claim about the second clause (the chi-square law on the sphere).

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture2805/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000002805.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C2805.schilder_rigidity_false`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000002805 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
