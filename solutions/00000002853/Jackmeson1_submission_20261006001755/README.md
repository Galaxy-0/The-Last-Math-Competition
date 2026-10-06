# Disprove conjecture 00000002853: cactus rank already falls below Waring rank in degree 3

- **Claim refuted.** The first conjunct: the least degree in which cactus rank drops below (Waring) rank is 5. It already happens in degree 3; refuting this conjunct refutes the conjunction (the vague "multi-point splitting" conjunct is not addressed).
- **Witness.** F = x₀²x₁ over ℂ. The double point with ideal (y₁²) is homogeneous and saturated, has Hilbert function 2 in every degree t ≥ 1, and lies in F^⊥ (for differentiation, and also for contraction), so the cactus rank of F is ≤ 2.
- **Waring rank.** Exactly 3: 6x²y = (x+y)³ − (x−y)³ − 2y³, and x²y is not a sum of two cubes of linear forms.
- **Faithful definitions.** Cactus rank = the least length of a zero-dimensional apolar subscheme (a saturated homogeneous ideal with eventually constant Hilbert function, contained in F^⊥); apolarity g∘F = Σ g_m ∂^m F via Mathlib's `pderiv`; Waring rank = the least number of d-th powers of linear forms; both as infima in ℕ∞, matched to retrieved and quoted definitions (Bernardi–Ranestad Definition 1, Bernardi–Taufer, Wikipedia). The monomial-ideal Hilbert function code is reused from our package for 00000000539.
- **Scope.** Lean covers binary forms (n = 2), refuting the "all forms" and "every fixed n" readings; that degrees 1 and 2 never separate (so the minimum is exactly 3) and the border-rank / general-form readings are not formalized.
- **Main theorem.** `C2853.conjecture_false` (3 ∈ separatingDegrees ∧ ¬ IsLeast separatingDegrees 5 ∧ sInf separatingDegrees ≤ 3), with separatingDegrees restricted to positive degrees (the coefficient-free Waring-rank definition is standard only for d > 0).
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 391 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture2853/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000002853.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C2853.conjecture_false`, `C2853.F0_separates`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-06): no solution folder for 00000002853 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
