# Solution Review — Conjecture 00000002333 (PR 404)

**Submission:** ziangni-sys — `ziangni-sys_submission_20261004044035`
**Reviewer:** competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-04

## Checklist results
- Conjecture read: yes — real Bézout number claimed as upper bound for solution count of real algebraic systems: (d/√m)^m · e^{1/2}, tight for balanced random systems
- LaTeX: proof.tex recompiled in /tmp/tlmc-review5/scratch/pr-404 with pdflatex (2 passes), exit 0, 0 errors, 2 pages; shipped proof.pdf is a real PDF 1.5 (Tectonic-built per verification/tectonic.log); verification/ logs consistent with my reproduction
- Lean build: exit 0 ("Build completed successfully", 2795 jobs); only output is 4 `#print axioms` info lines, each exactly [propext, Classical.choice, Quot.sound]
- Forbidden content: grep over own Main.lean for sorry/admit/native_decide/`axiom `/unsafe/implemented_by/extern/skipKernelTC: no hits; verification/checks.txt records the same audit
- Auxiliary code: no executable scripts (README/checks.txt state all evidence is proved in Lean — confirmed, no #eval/decide needed); independent python3 re-derivation: roots {±1}² = 4 points, all satisfy both equations, min sup-norm pairwise distance 2 (isolated), both total degrees 2, B(2,2) = (2/√2)²·e^{1/2} = 2√e ≈ 3.2974 < 4 — matches the Lean theorem exactly
## Semantic audit
Conjecture literal claim (EN): "The real Bézout number is an upper bound for the solution count of real algebraic systems. Conjecture: The improved bound is (d/√m)^{m}·C (C = e^{1/2})". The submission refutes exactly this universal upper-bound clause.

Lean encoding is faithful to the conjecture's own objects:
- `def equation (i : Fin 2) : MvPolynomial (Fin 2) ℝ := X i ^ 2 - C 1` — genuine multivariate polynomials over ℝ in 2 variables; `theorem equation_degree : (equation i).totalDegree = 2` proves d = 2 via the actual `totalDegree`.
- `theorem solution_iff (x : Point) : IsSolution x ↔ ∀ i, x i = -1 ∨ x i = 1` — complete root classification (no extra solutions), where `IsSolution x := ∀ i, MvPolynomial.eval x (equation i) = 0` is actual evaluation.
- `def rootEquiv : (Fin 2 → Bool) ≃ {x : Point // IsSolution x}` with both inverse laws proved; `theorem solution_count : Fintype.card {x : Point // IsSolution x} = 4` — the count of the ENTIRE solution set, not an asserted list.
- `theorem roots_isolated (x y : ...) (h : dist x.val y.val < 1) : x = y` — metric isolation in the sup-norm pi metric (via `norm_le_pi_norm`), so the count is a count of isolated roots, meeting even the customary isolated-roots restriction; independently confirmed (min pairwise sup-distance = 2).
- `def proposedBound (d m : ℕ) : ℝ := ((d : ℝ) / Real.sqrt m) ^ m * Real.exp (1 / 2)` — the literal conjecture formula with the actual real sqrt/exp; `bound_at_two : proposedBound 2 2 = 2 * Real.exp (1 / 2)`; `exp_half_lt_two` from Mathlib's `Real.exp_one_lt_d9`.
- Final theorem `claimed_bound_fails : proposedBound 2 2 < (Fintype.card {x : Point // IsSolution x} : ℝ)` — direct contradiction of the upper-bound claim: bound < 4 = actual isolated real solution count.

Not vacuous and not degenerate: the counterexample is a square system (m = 2 equations = 2 variables, so no ambiguity in m), equal degrees (so even "balanced"), all roots simple and isolated. d = m = 2 is the smallest nontrivial case, not an edge case; the conjecture text carries no restriction excluding it (both languages call the quantity an upper bound for the solution count). Unlike the rejected numeric-only submissions, every fact here (degree, classification, cardinality, isolation, the analytic inequality 2√e < 4) is a proved Lean theorem over genuine Mathlib structures, with only the three standard axioms. The "tightness" clause cannot rescue a bound that already fails; the submission correctly targets the authoritative upper-bound clause.
## Issues found
none blocking. (Minor: none — parameter readings d, m coincide in this example.)
## Verdict rationale
The Lean project proves, from genuine multivariate polynomials and the literal bound formula, that the system x₀²−1 = x₁²−1 = 0 has exactly 4 isolated real solutions of degree-2 equations while the proposed bound gives 2√e ≈ 3.297 < 4 — a complete, non-degenerate disproof of the conjecture's upper-bound claim. Build is clean with only standard axioms; the LaTeX compiles and matches the shipped PDF; the arithmetic was independently re-derived and confirmed.

## Disposition
APPROVED — merged into main (PR 404). Independent fresh rebuild of the Lean project (Mathlib-pinned, exit 0; only standard foundational axioms; no sorry/native_decide/extra axioms), LaTeX recompilation, auxiliary-script re-runs where shipped, independent recomputations, and a semantic audit confirming the Lean theorem establishes or refutes the conjecture as stated in both language versions.
