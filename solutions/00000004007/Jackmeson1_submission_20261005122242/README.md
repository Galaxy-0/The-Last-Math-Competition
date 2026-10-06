# Disprove conjecture 00000004007: p-variation violates ‖X+Y‖ ≤ (‖X‖^q + ‖Y‖^q)^{1/q}

- **Definition.** The p-variation is defined in Lean as the p-th root of the supremum, over partitions a = t₀ < … < tₙ = b, of Σ‖X(tᵢ) − X(tᵢ₋₁)‖^p, valued in [0, ∞] (Mathlib has no p-variation).
- **Homogeneity.** It is 1-homogeneous (`pVar_smul`), so for Y = X the left side is 2‖X‖ while the right side is 2^{1/q}‖X‖ < 2‖X‖ since q > 1 (`fails_at_diagonal`, for any path with finite nonzero p-variation in any real normed space).
- **Witness.** X(t) = t on [0,1] has p-variation exactly 1 (`pVar_id`), so ‖X+Y‖ = 2 > 2^{1/q} for every p > 1 with Hölder conjugate q (Mathlib's `Real.HolderConjugate`).
- **Other readings.** The case p = 1 (q = ∞, right side read as max), the root-free normalisation and the concatenation reading of X+Y also fail. Not addressed: 0 < p < 1 and p = ∞.
- **Main theorems.** `conjecture_00000004007_false`, `conjecture_00000004007_false'`, `conjecture_00000004007_false_one`.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 266 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

**Previous submission and its error (README rule 2).** PR #42 (earthking11) was merged, then removed in re-audit 541cf4fb with the reason "pure powers-of-2 arithmetic; p-variation unformalized". Its mathematics (take Y = X; the p-variation is 1-homogeneous, so ‖X+X‖ = 2‖X‖ > 2^{1/q}‖X‖) is correct, but its Lean file proved only natural-number facts such as ¬(2^2 ≤ 2) and 2 < 2^q, and its own docstring said "There is no real-valued p-variation formalised here". This submission formalizes partitions a = t₀ < … < tₙ = b and the p-variation as the p-th root of the supremum of the increment sums (values in [0, ∞]). It proves homogeneity and the diagonal failure for every path of finite nonzero p-variation in any real normed space, and computes the p-variation of t ↦ t on [0, 1] exactly as 1. It then states the conjecture's inequality with Mathlib's `Real.HolderConjugate p q` and refutes it for every real p > 1, for p = 1 with q = ∞ (read as max), for the root-free normalisation, and for the concatenation reading of X + Y.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture4007/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000004007.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `Tlmc4007.conjecture_00000004007_false`, `Tlmc4007.fails_at_diagonal`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000004007 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
