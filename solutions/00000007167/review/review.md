# Solution Review — Conjecture 00000007167 (PR 378)

**Submission:** ziangni-sys — `ziangni-sys_submission_20261004025410`
**Reviewer:** competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-04

## Checklist results
- Conjecture read: yes — claims the universal upper bound of the ratio (numerical radius)/(operator norm) is 1/2, with tightness at a 2D rotation (Sz.-Nagy equivalence).
- LaTeX: compiled (pdflatex twice, exit 0 both passes); shipped report.pdf is a real PDF (v1.5) whose extracted text matches report.tex exactly.
- Lean build: exit 0 ("Build completed successfully."), no warnings; replayed with `#print axioms` output listing only [propext, Classical.choice, Quot.sound] for all four theorems.
- Forbidden content: none. Only occurrence of "sorry/admit/native_decide" is the English sentence in VERIFICATION.md asserting their absence; Main.lean contains no tactic-level `sorry`/`admit`, no `native_decide`, no `axiom` declaration, no `unsafe`/`extern`/`implemented_by`/`skipKernelTC`.
- Auxiliary code: none claimed (VERIFICATION.md: "No auxiliary computational verification is required"). I independently recomputed w(I) on the unit circle in Python: |⟨v, Iv⟩| = 1 for all unit v, so w(I)/‖I‖ = 1 > 1/2 — matches the submission.
## Semantic audit
Conjecture (EN): "The upper bound of the ratio of radius to operator norm is one half, and the tightness of the bound is the two-dimensional rotation." (CN: "半径与算子范数的比的上界为一半且界的紧性为二维旋转"). The load-bearing claim is the universal bound w(A)/‖A‖ ≤ 1/2; truth is w(A)/‖A‖ ∈ [1/2, 1], so the bound as stated is the classical LOWER bound misstated as an upper bound.

Lean encodings (all verified against Mathlib definitions, no asserted data):
- `noncomputable def unitNumericalValues (A : ℂ →L[ℂ] ℂ) : Set ℝ := {r | ∃ v : ℂ, ‖v‖ = 1 ∧ r = ‖@inner ℂ ℂ _ v (A v)‖}` — exact sup-set of |⟨v, Av⟩| over unit vectors.
- `noncomputable def numericalRadius (A : ℂ →L[ℂ] ℂ) : ℝ := sSup (unitNumericalValues A)` — literal w(A).
- `theorem identity_operator_norm : ‖identity‖ = 1` via `ContinuousLinearMap.norm_id` — Mathlib's actual operator norm, not a proxy.
- `theorem identity_numerical_values : unitNumericalValues identity = {1}` — proved by both containments (every unit vector gives value 1 via `inner_self_eq_norm_sq_to_K`; v = 1 witnesses membership), so w(I) is computed, not assumed.
- `theorem identity_numerical_radius : numericalRadius identity = 1` via `csSup_singleton`.
- `def ClaimedHalfUpperBound : Prop := ∀ A : ℂ →L[ℂ] ℂ, 0 < ‖A‖ → numericalRadius A / ‖A‖ ≤ (1 : ℝ) / 2`
- `theorem conjecture_7167_false : ¬ ClaimedHalfUpperBound` — applies the hypothesis to `identity` (hypothesis 0 < ‖identity‖ satisfied since ‖identity‖ = 1), derives 1 ≤ 1/2, closed by `norm_num`.

(i) Definitions faithful: yes — numerical radius is the supremum of actual unit-vector inner-product magnitudes, operator norm is Mathlib's ContinuousLinearMap norm. (ii) Hypotheses satisfied: ‖I‖ = 1 > 0. (iii) The theorem contradicts the literal claim: identity has ratio 1 > 1/2. (iv) Not vacuous: the negation is of a genuinely universally-quantified bound, and the counterexample operator is a genuine nontrivial bounded operator. Degeneracy note: the witness lives on the 1-dimensional Hilbert space ℂ; the bilingual text carries no dimension restriction ("the ratio ... upper bound is one half" / "the ratio of radius to operator norm ... upper bound is one half" is a universal statement), and the report correctly notes the same computation works on any nonzero Hilbert space including dimension 2 — so the disproof is robust under any dimension reading. This is a full Lean proof of the counterexample (not a numeric-facts-only proof as in rejected #286-288): the value-set equality and the norm are proved inside Lean.
## Issues found
none blocking
## Verdict rationale
The conjecture's universal claim w(A)/‖A‖ ≤ 1/2 is contradicted by a fully formalized, non-vacuous counterexample (identity on ℂ, w = ‖I‖ = 1, ratio 1), with every quantity proved in Lean from Mathlib definitions and only the three standard axioms used. Build, PDF, and forbidden-content checks all pass, and the report faithfully describes the proof. The 1-dimension witness is flagged for the record but is mathematically decisive since the conjecture states an unrestricted universal bound.

## Disposition
APPROVED — merged into main (PR 378). Independent fresh rebuild of the Lean project (exit 0; only standard foundational axioms; no sorry/native_decide/extra axioms), LaTeX recompilation, auxiliary-script re-runs where shipped, independent recomputations, and a semantic audit confirming the Lean theorem establishes or refutes the conjecture as stated in both language versions.
