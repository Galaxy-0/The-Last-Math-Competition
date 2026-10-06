# Disprove conjecture 00000002251: ker Δ_c on meromorphic functions has dimension ≥ 2 for every c

- **Operator.** Δ_c f = f(·+c) − f is defined in Lean as a ℂ-linear endomorphism of `MeroFun = {f : ℂ → ℂ | Meromorphic f}` (Mathlib `fwdDiff c`).
- **Main theorem.** `rank_ker_diffOp_gt_one : ∀ c, 1 < Module.rank ℂ (ker Δ_c)`. Witnesses: 1 and exp(2πiz/c) for c ≠ 0 (values at 0 and c/2 are (1,1) and (1,−1)); 1 and z for c = 0.
- **Germ model.** `indep_mod_codiscrete`: the independence survives identifying functions that agree off a discrete set.
- **Spectrum (c ≠ 0).** `spectrum ℂ Δ_c = ℂ∖{−1}`: every μ ≠ −1 has the eigenfunction e^{bz} with b = log(1+μ)/c, and −1 − Δ_c = −shift is bijective. The spectrum is uncountable, so it is not {2 sin(kc/2) : k ∈ ℤ} (`spectrum_ne_sine_set`).
- **Previous PR #270.** It was merged, then removed in the re-audit 541cf4fb ("4-point cyclic shadow; meromorphic kernel prose-only"): its Lean only proved facts about a 4-periodic `Nat → Int×Int` table and contained no meromorphic functions, no Δ_c and no kernel. Its spectrum claim ℂ∖{0} is also wrong: the correct set is ℂ∖{−1}, and 0 is an eigenvalue (the kernel's). This submission formalizes the actual objects.
- **Scope.** Not refuted: restricted readings (polynomials, rational functions, order < 1, 2π-periodic trigonometric polynomials), where the kernel can be the constants.
- **Main theorems.** `Tlmc2251.rank_ker_diffOp_gt_one`, `Tlmc2251.conjecture_2251_refuted`.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 221 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture2251/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000002251.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `Tlmc2251.rank_ker_diffOp_gt_one`, `Tlmc2251.conjecture_2251_refuted`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000002251 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
