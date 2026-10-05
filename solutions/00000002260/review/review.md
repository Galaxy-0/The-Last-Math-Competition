# Solution Review — Conjecture 00000002260 (PR 557)

**Submission:** ziangni-sys — `ziangni-sys_submission_20261004221500`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-04

## Checklist results
- Official bilingual conjecture read in full from `conjectures/00000002260.md`: "the explicit realization of the infimum relation dim_H J(f) ≥ ρ/2 between the Hausdorff dimension of the Julia set and the order of entire functions", with no restriction on ρ in either language. No SOURCE.md; `verification/original.md` is byte-identical (`diff` clean) to the official file.
- LaTeX `proof.tex` read in full; independently rebuilt with `latexmk -pdf` (pdflatex) — compiles cleanly. pypdf extraction of both PDFs matches exactly (1800 = 1800 chars) after stripping the engine-dependent page-number glyphs; the only raw difference is that Tectonic and pdflatex break the page at different lines, so the page-number digits interleave at different positions. Content is identical.
- Fresh `lake build` on Lean v4.19.0, Mathlib pinned at c44e0c8e: **Build completed successfully**, 2802 targets, zero errors, two harmless lint warnings (unused variable, unnecessary simpa).
- Axiom audit: 5 `#print axioms` lines (`entire`, `maximum_modulus_eq`, `actual_order`, `dimension_upper`, `counterexample`) — all `[propext, Classical.choice, Quot.sound]` only.
- Grep for `sorry`, `native_decide`, `axiom` declarations, `unsafe`, `@[implemented_by]`, `extern`, `admit`: no hits in the Lean sources.
- Auxiliary code: none; the maximum-modulus claim was instead re-verified numerically (sampling Re(z⁵) on circles |z| = 1.5, 2, 3 gives max Re = r⁵ exactly, so M(r) = exp(r⁵)).
- `metadata.csv` on main marks 00000002260 neither proven nor disproven (unsolved).

## Semantic audit
The conjecture asserts the lower-bound relation dim_H J(f) ≥ ρ/2 for entire functions as an infimum-type law; a lower bound of this shape is naturally a universal claim over the class, and the official text imposes no cap on the order ρ (it never says ρ ≤ 4, which is the feasibility threshold since dim_H ≤ 2 in the plane). The submission refutes the unrestricted statement with a single explicit function: f(z) = exp(z⁵). The mathematics is elementary and airtight. f is entire (composition of exp with the polynomial z⁵). Its maximum modulus on |z| ≤ r is exactly M(r) = exp(r⁵): |exp(z⁵)| = exp(Re z⁵) ≤ exp(|z|⁵) ≤ exp(r⁵), with equality at the real point z = r on the boundary circle (numerically re-confirmed). Hence log log M(r) / log r = log(r⁵)/log r = 5 identically for r > 1, the limit exists and equals 5, and the limsup order is ρ(f) = 5. Since the Julia set of an entire function is by definition a subset of ℂ, and ℂ is a two-dimensional real Euclidean space, dim_H J(f) ≤ dim_H ℂ = 2 < 5/2 = ρ(f)/2. The conjectured inequality is therefore violated — indeed no subset of the plane whatsoever can satisfy it for this f.

The formalization is faithful and methodologically honest about the one thing it does not do: it does not define a surrogate "Julia set". Instead `dimension_upper` proves the ambient theorem ∀ S : Set ℂ, dimH S ≤ 2 (via `dimH_mono` and `Real.dimH_univ_eq_finrank`/`Complex.finrank_real_complex`), and `every_planar_set_refutes_bound` combines it with `actual_order` to show ¬(ofReal(growthOrder f / 2) ≤ dimH S) for every planar S. Applying this to the genuine J(f) — a subset of ℂ by the uncontroversial definition of the Julia set of an entire function — yields exactly the negation of the conjectured relation. All the analytic ingredients are the genuine articles: `maximumModulus` is the actual sSup over the closed disk with attainment proved, `growthOrder` is the standard limsup of log log M / log r, and `actual_order` computes it via the eventually-constant quotient. The ENNReal coercion `ofReal (ρ/2)` correctly handles the extended-real Hausdorff dimensions, and the strict inequality 2 < ofReal(5/2) is proved by norm_num. The report's scope paragraph accurately states what is and is not refuted (it does not claim a dimension formula for this Julia set, and leaves alone any bound stated with restrictions on ρ). The quantifier structure of the disproof matches the universal lower-bound reading of the official text.

The report and the Lean theorems agree point by point, and the README/validation logs describe the same content.

## Issues found
None blocking. (Two non-fatal lint warnings; cross-engine pagination difference in the PDF comparison with identical content.)

## Verdict
APPROVED. The submission disproves the unrestricted order–dimension inequality dim_H J(f) ≥ ρ/2 by exhibiting the explicit entire function exp(z⁵) of order 5, whose ρ/2 = 5/2 exceeds the planar Hausdorff-dimension ceiling of 2 that any Julia set must obey; every mechanical check passes and the formalization uses genuine definitions throughout, with the ambient universal theorem correctly covering the genuine Julia set.
