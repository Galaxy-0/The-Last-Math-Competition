# Solution Review — Conjecture 00000008841 (PR 392)

**Submission:** ziangni-sys — `ziangni-sys_submission_20261004035046`
**Reviewer:** competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-04

## Checklist results
- Conjecture read: yes — "Weak convergence of asymptotically nonexpansive sequences always holds in Hilbert space; strong convergence exceptions delimited by the demiclosedness principle" (disproof submission).
- LaTeX: compiled with pdflatex twice, exit 0 both passes, no errors, no overfull boxes; shipped report.pdf is a genuine 2-page PDF whose extracted text matches report.tex content.
- Lean build: `lake build` exit 0; only output was the two `#print axioms` info lines ([propext, Classical.choice, Quot.sound]); no warnings.
- Forbidden content: grep for sorry/admit/native_decide/axiom decls/unsafe/implemented_by/extern/skipKernelTC over lean/Main.lean and lakefile.lean — no hits. `#print axioms conjecture_00000008841` and `interval_geometry` show only the three standard logical axioms.
- Auxiliary code: none present and none needed (README/verification.txt state no computational dependencies); verification.txt records match my independently reproduced build and axiom audit.
## Semantic audit
Conjecture literal claim (EN): "Weak convergence of asymptotically nonexpansive sequences always holds in Hilbert space; and strong convergence exceptions are delimited by the demiclosedness principle." The universal weak-convergence assertion is the first conjunct; refuting it refutes the conjunction.

Lean encodings (namespace `AsymptoticIteration8841`):
- `def AsymptoticallyNonexpansive (T : ℝ → ℝ) : Prop := ∃ k : ℕ → ℝ, (∀ n, 1 ≤ k n) ∧ Tendsto k atTop (𝓝 1) ∧ ∀ n x y, dist (T^[n] x) (T^[n] y) ≤ k n * dist x y` — faithful to the standard definition (Lipschitz constants ≥ 1 tending to 1 on the iterates), stated on ℝ, a real Hilbert space.
- `def WeaklyConverges (u : ℕ → ℝ) (a : ℝ) : Prop := ∀ f : ℝ →L[ℝ] ℝ, Tendsto (fun n => f (u n)) atTop (𝓝 (f a))` — the standard weak-convergence definition quantified over ALL continuous linear functionals (not a cherry-picked one).

Final theorem: `theorem conjecture_00000008841 : AsymptoticallyNonexpansive reflection ∧ (∀ n, Isometry (reflection^[n])) ∧ reflection 0 = 0 ∧ Set.MapsTo reflection (Set.Icc (-1:ℝ) 1) (Set.Icc (-1:ℝ) 1) ∧ (∀ n, orbit n ∈ Set.Icc (-1:ℝ) 1) ∧ ¬ ∃ a, WeaklyConverges orbit a` with `orbit n := reflection^[n] 1` (`orbit` uses genuine `Function.iterate`, not a value table; `orbit_even`/`orbit_odd` prove 1,−1 alternation by induction).

The counterexample T(x) = −x on ℝ: every iterate is an isometry (proved: `iterate_isometry`), so asymptotic nonexpansiveness holds with k_n = 1 → 1; T fixes 0 and preserves the nonempty closed bounded convex set [−1,1] (so no missing hypothesis that the text supplies is exploited); yet the orbit alternates 1, −1 and the identity functional forces 1 = −1 for any weak limit (`orbit_not_weakly_convergent`). Not vacuous: all hypotheses the conjecture's own definition carries (asymptotic nonexpansiveness, Hilbert space setting, bounded orbit) are satisfied, and the negation of the universal claim is established. ℝ is a Hilbert space; the conjecture text carries no dimension restriction, so the 1-dimensional example is legitimate. This is the classical 2-cycle counterexample (any averaged/asymptotic-regularity hypothesis would be needed to rescue the claim, and none is present in the text). The demiclosedness clause is untouched but the conjunction is already falsified.
## Issues found
none blocking
## Verdict rationale
The Lean formalization is complete (builds clean, only standard axioms), faithfully encodes asymptotic nonexpansiveness and weak convergence per standard definitions, and proves a genuine, non-vacuous counterexample (negation on ℝ with alternating Picard orbit) to the literal universal weak-convergence claim. The LaTeX report accurately reproduces the conjecture and the construction, compiles cleanly, and the shipped PDF matches. All checklist items pass.

## Disposition
APPROVED — merged into main (PR 392). Independent fresh rebuild of the Lean project (Mathlib-pinned, exit 0; only standard foundational axioms; no sorry/native_decide/extra axioms), LaTeX recompilation, auxiliary-script re-runs where shipped, independent recomputations, and a semantic audit confirming the Lean theorem establishes or refutes the conjecture as stated in both language versions.
