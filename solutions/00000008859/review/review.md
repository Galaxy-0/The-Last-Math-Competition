# Solution Review — Conjecture 00000008859 (PR 570)

**Submission:** ziangni-sys — `ziangni-sys_submission_20261004204655`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-04

## Checklist results
- Official bilingual conjecture `conjectures/00000008859.md` read in full. It is a four-clause conjunction; the first clause asserts the supremum of inertial parameters is *always* the reciprocal of the inverse norm of the splitting operator. No SOURCE.md present (absent, not failed).
- LaTeX: `report.tex` rebuilt from scratch with `latexmk -pdf` (clean, 2 pages). MuPDF text comparison of shipped (Tectonic) vs rebuilt PDF: identical content; residual differences are only big-delimiter glyph extraction (`\big(` parens) and one ﬀ ligature.
- Lean: fresh `lake build`, lean4 v4.19.0, Mathlib pinned at `c44e0c8ee63ca166450922a373c7409c5d26b00b` — **0 errors, 0 warnings**.
- Axioms: `Main.lean` prints axiom audits for all ten results (`A_maximal`, `zero_unique`, `resolvent_equation`, `genuine_inverse`, `bound_value`, `first_update`, `actual_inertial_recurrence`, `state_geometric`, `all_initials_converge`, `claimed_supremum_false`); every one depends only on `[propext, Classical.choice, Quot.sound]`. No `sorry`/`native_decide`/`axiom`/`unsafe`/`admit` anywhere.
- Auxiliary code: none (README/VERIFICATION prose only).
- Repo metadata: conjecture unsolved; submission claims a disproof.

## Semantic audit
The conjecture's first clause is a universal formula: sup of admissible inertial parameters = ‖T⁻¹‖⁻¹ for the splitting operator T. The submission's counterexample takes A(x) = 9x on the Hilbert line — a bounded, everywhere-defined, maximal monotone operator (maximality proved constructively: any (x,u) monotonically related to the whole graph must satisfy u = 9x, by testing y = x + (u−9x)/18 which forces −(u−9x)²/36 ≥ 0) — whose resolvent T = (I+A)⁻¹ is the map p ↦ p/10, with genuine two-sided inverse 10I and operator norm ‖T⁻¹‖ = 10. The proposed bound is thus b* = 1/10. For the standard constant-inertia splitting iteration x_{k+1} = T(x_k + β(x_k − x_{k−1})) — formalized as the first coordinate of an actual orbit of the state map on ℝ² with the genuine product sup norm, and proved in Lean to satisfy exactly this recurrence for every initial pair — the choice β = 1/2 (squarely inside the conventional [0,1) range) gives the state map F(x,y) = (3/20·x − 1/10·y, x/2), a contraction: ‖F(x,y)‖∞ ≤ max(1/4, 1/2)·‖(x,y)‖∞ = (1/2)‖(x,y)‖∞. Hence ‖z_k‖ ≤ 2⁻ᵏ‖z_0‖ and x_k → 0 geometrically for *every* pair of initial values, so 1/2 belongs to the admissible set 𝒜 = {β | ∀ initial pairs, x_k → 0}. Since 1/2 > 1/10 = b*, the proposed value is not even an upper bound of 𝒜, and `claimed_supremum_false : ¬ IsLUB admissible (1/10)` holds — no assumption about the true supremum's value, boundedness, or attainment is needed.

I verified the mathematics independently by hand and numerically: simulating the iteration at β = 1/2 from extreme initials (x₀ = 10⁶, x₋₁ = −10⁶) drives the error to ~10⁻¹²⁵ within 200 steps; the Jury/root analysis of the characteristic polynomial λ² − (1/10)(1+β)λ + (1/10)β shows stability exactly for β < 10, with |roots| = 0.99949 at β = 9.99, 1.0000 at β = 10 (marginal), 1.0005 at β = 10.01 — so the genuine supremum of 𝒜 is 10 = ‖T⁻¹‖, decisively not its reciprocal 1/10, confirming the refutation is robust (every β ∈ [1/10, 10) already witnesses it). The formalization is faithful: real continuous linear maps with a proved two-sided inverse, the actual resolvent equation x + Ax = p ⟺ x = Tp, the exact recurrence derived from the orbit (not assumed), admissibility quantified over all initial pairs as the stability reading of the definition clause, and the negation of the IsLUB property at the proposed constant. The remaining three clauses (oscillation counterexamples, Ω(1/√ε) complexity with Nesterov term-matching, in-bound constant-multiple rate) form a conjunction with the first clause, so refuting the first clause refutes the conjecture; the report states this and does not overreach.

## Issues found
None blocking. (Tectonic vs pdflatex delimiter-glyph extraction differences only; content verified identical.)

## Verdict
APPROVED. The counterexample is mathematically correct and numerically reconfirmed, the formalization faithfully negates the conjecture's universal first clause at a concrete maximal-monotone splitting operator with the exact standard inertial iteration, the build is clean with zero warnings and only the three standard axioms, and scope claims match what is actually proved.
