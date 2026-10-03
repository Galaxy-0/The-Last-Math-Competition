# Solution Review — Conjecture 00000007780 (PR 323)

**Submission:** feiyuceng06-prog — `feiyuceng06-prog_submission_20261003110312`
**Reviewer:** competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-03

## Checklist
- [x] LaTeX source and PDF present
- [x] Lean 4 project compiles completely (lake build, exit 0, Mathlib v4.33.1)
- [x] No `sorry`, no `native_decide`, no extra axioms (`#print axioms` exactly `[propext, Classical.choice, Quot.sound]`)
- [x] Submission matches the conjecture's objects and literal statement

## Conjecture (verbatim summary)
For any quadratic polynomial f and power map z^d on P¹(Q̄): (C1) the common preperiodic set has cardinality ≤ 2·v(d), v(d) the prime-factor count of d; (C2) if f is neither Chebyshev nor monomial, the set has ≤ 3 points.

## What the submission proves
Counterexample f(z) = z² − 1, d = 2 (so 2·v(2) = 2 under both the ω and Ω conventions): the four points 0, 1, −1, ∞ are preperiodic for both maps — under f: 0 → −1 → 0, 1 → 0, ∞ fixed; under z²: 0, 1, ∞ fixed, −1 → 1. So the common set has ≥ 4 > 2 points, refuting (C1). f is not affinely conjugate to z² (evaluate at z = ±1, eliminate β, get α² = 0) nor to ±(2z² − 1) (evaluate at 0, ±1), and the common set has 4 > 3 points, refuting (C2). Lean: `subset_commonPrep`, `four_le_encard`, `not_isMonomial`, `not_isChebyshev`, `not_claim1`, `not_claim1'`, `not_claim2`, `conjecture_00000007780_false : ¬ (Claim1 ∨ Claim1') ∧ ¬ Claim2`.

## Verification notes
`lake build` exit 0; axiom audit clean. Faithful arithmetic dynamics: P¹(Q̄) = `Option (AlgebraicClosure ℚ)` with ∞ fixed, `IsPreperiodic` via `Function.IsPeriodicPt` after `F^[m]`, both generic in the coefficients and d. All four orbit certificates are kernel-checked iterates; distinctness of the four points (including 1 ≠ −1 in Q̄) is proven. The non-conjugacy eliminations were re-derived independently by the reviewer and match. d ≥ 2 is the natural reading of "power map" and only weakens the claims. LaTeX consistent; PDF present.

## Verdict
APPROVED — merged into main.
