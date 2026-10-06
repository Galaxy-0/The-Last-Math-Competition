# Disprove conjecture 00000009682: two algebraically independent U-numbers exist

- **Claim refuted.** The third conjunct: algebraically independent sets of U-numbers have "dimension exactly 1, with no two-dimensional U families" (dimension read as transcendence degree over ℚ); this refutes the conjunction. The other conjuncts are written into the formal statement but not used.
- **Definitions.** Following Wikipedia "Transcendental number theory" (Mahler's classification, retrieved and quoted): m(x,n,H) = min nonzero |P(x)| over P ∈ ℤ[X] with deg ≤ n and height ≤ H; ω(x,n,H) = −log m/(n log H); ω(x,n) = limsup_H in EReal; a U-number is transcendental with ω(x,n) = ∞ for some n ≥ 1.
- **Liouville ⇒ U.** P = bX − a gives ω(x,1) = ∞ (`liouville_isUNumber`).
- **Two independent U-numbers.** x = `liouvilleNumber 10` (Mathlib's sum starts at i = 0, so x = 1/10 + Liouville's constant). Liouville numbers are residual (Mathlib); the reals algebraic over the countable algebra ℚ[x] form a countable set; by Baire there is a Liouville y transcendental over ℚ[x], so {x, y} is algebraically independent over ℚ, in ℝ and in ℂ (`exists_two_indep_U`).
- **Refutation.** A 2-element algebraically independent set of U-numbers exists, and the supremum of such sizes is ≥ 2 (`two_le_iSup_real`, `two_le_iSup_complex`).
- **Not covered.** "Dimension" as Hausdorff dimension; readings restricted to U_n with n ≥ 2 (both witnesses have degree 1).
- **Main theorems.** `C9682.not_conjectureReal`, `C9682.not_conjectureComplex`.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 300 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture9682/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000009682.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C9682.not_conjectureReal`, `C9682.not_conjectureComplex`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000009682 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
