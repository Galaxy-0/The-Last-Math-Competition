# Solution Review — Conjecture 00000008855 (PR 386)

**Submission:** ziangni-sys — `ziangni-sys_submission_20261004032901`
**Reviewer:** competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-04

## Checklist results
- Conjecture read: yes — "The proximal operator of sparse penalties is always soft thresholding; and the convergence rate of thresholded splitting is O(1/t) plus a logarithmic correction" (conjunction; disproving either conjunct refutes it).
- LaTeX: compiled with pdflatex twice in scratch, exit 0 both passes, no errors; shipped report.pdf is a genuine 1-page PDF (gs renders it) whose text matches the recompiled output up to font-ligature extraction artifacts (shipped built with Tectonic/lmodern).
- Lean build: exit 0 ("Build completed successfully", 745 jobs replayed). No warnings. `#print axioms` output for `prox_two_iff`, `prox_one_iff`, `conjecture_8855_false` = exactly [propext, Classical.choice, Quot.sound].
- Forbidden content: grep for sorry/admit/native_decide/`axiom `/unsafe/implemented_by/extern/skipKernelTC over Main.lean + lakefile.lean: no hits.
- Auxiliary code: none beyond Lean (README's `verify` steps are the build itself). VERIFICATION.md claims independently confirmed: build exit 0, axiom sets, clean grep. Recompiled PDF verified. Mathlib pinned at c44e0c8e, Lean 4.19.0 as claimed.
## Semantic audit
Conjecture's literal claim (EN/CN identical in content): 稀疏罚的邻近算子恒为软阈值 ("the proximal operator of sparse penalties is ALWAYS soft thresholding"). The submission takes the canonical scalar sparse penalty — the nonzero-count penalty —
`def sparsePenalty (y : ℝ) : ℝ := if y = 0 then 0 else 1`
and the exact unit-parameter proximal objective `objective x y = (y-x)^2/2 + sparsePenalty y` with set-valued prox correctly encoded as the global-minimum relation `def Prox (x y : ℝ) : Prop := ∀ z : ℝ, objective x y ≤ objective x z` (y ∈ argmin). It then proves:
- `theorem prox_two_iff (y : ℝ) : Prox 2 y ↔ y = 2` (unique proximal value 2 at input 2: F₂(2)=1 < F₂(0)=2, and 1+(y−2)²/2 > 1 otherwise)
- `theorem prox_one_iff (y : ℝ) : Prox 1 y ↔ y = 0` (unique proximal value 0 at input 1: F₁(0)=1/2 < 1+(y−1)²/2)
- standard piecewise soft threshold `softThreshold τ x` (correct for τ ≥ 0), and the decisive
- `theorem conjecture_8855_false : ¬ (∃ tau : ℝ, 0 ≤ tau ∧ ∀ x : ℝ, Prox x (softThreshold tau x))`
Proof: agreement at x=2 forces τ=0 (`soft_at_two_forces_zero`), but S₀(1)=1 ≠ 0, contradicting `prox_one_iff`. Both iff-characterizations quantify over every real competitor (nlinarith on sq_nonneg), so the minima are genuinely global, not table lookups. Hypotheses: none beyond the definition; the theorem is NOT vacuous — ℓ₀ is a bona fide sparsity penalty (the report explicitly notes the conjecture imposes no convexity, and flags the nonconvexity; the ℓ₁ soft-threshold result is not claimed to fail). Refuting the first conjunct of "恒为/always" via one explicit sparse penalty suffices; the report honestly states the rate clause is not needed. This is the standard, correct hard-vs-threshold counterexample (ℓ₀ prox = hard thresholding).
## Issues found
none blocking
## Verdict rationale
The Lean project builds cleanly with only the three standard axioms, the LaTeX report compiles and matches the shipped PDF, no forbidden content exists, and the formalization faithfully encodes the conjecture's objects (sparse penalty, proximal operator, soft thresholding) and proves a genuine, non-vacuous contradiction of the literal "always soft thresholding" claim. The mathematical content (ℓ₀ prox is hard thresholding, not soft) is correct.

## Disposition
APPROVED — merged into main (PR 386). Independent fresh rebuild of the Lean project (Mathlib-pinned, exit 0; only standard foundational axioms; no sorry/native_decide/extra axioms), LaTeX recompilation, auxiliary-script re-runs where shipped, independent recomputations, and a semantic audit confirming the Lean theorem establishes or refutes the conjecture as stated in both language versions.
