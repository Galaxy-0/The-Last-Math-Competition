# Solution Review — Conjecture 00000000240 (PR 633)

**Submission:** C0ldSmi1e — `C0ldSmi1e_submission_20261005124904`
**Reviewer:** independent competition reviewer (structure + build + semantic audit)
**Date:** 2026-10-06

## Checklist results
- Official conjecture read (bilingual): the statement asserts the Mahler lower bound `vol(K)vol(K°) ≥ 4ⁿ/n!` together with an equality classification "attained only by linear images of the cube or cross-polytope", with `(known for n ≤ 3)` as a parenthetical status remark. Shipped `conjecture.md` (and `verification/inputs/conjecture.md`) are byte-identical to `conjectures/00000000240.md`.
- LaTeX: `main.tex` rebuilt independently with `latexmk -pdf` (exit 0); 4 pages in both shipped and rebuilt PDFs; extracted text identical after glyph/whitespace normalization.
- Lean: `lake build` (Lean 4.19.0, pinned Mathlib) exits 0, no errors, no warnings.
- Axioms: all 61 `#print axioms` reports in the build are exactly `[propext, Classical.choice, Quot.sound]`, including the decisive `equality_classification_false`, `conjecture_00000000240_english_false`, `conjecture_00000000240_chinese_false`.
- Forbidden content: no `sorry`, `admit`, `native_decide`, `axiom`, `unsafe`, `implemented_by`, `extern` in the mathematical sources.
- Auxiliary code: `python3 reproduce.py` exits 0 and its output is byte-identical to `verification/reproduce.stdout`. It independently computes, in exact rational arithmetic, complete face lattices with supporting-facet certificates, primal/polar vertex-facet duality, barycentric determinant volumes (K: 12 vertices, 10 facets, vol 8/3; K°: 10 vertices, 12 facets, vol 4; product 32/3 = threshold), plus cube/cross reference volumes and a shear normalization check.
- Integrity: 57/57 files match `verification/SHA256SUMS.json`.

## Semantic audit
The official text claims, for symmetric convex bodies generally, both the lower bound and that equality is attained **only** by linear images of the cube or the cross-polytope; the parenthetical `(known for n ≤ 3)` records prior knowledge and does not restrict the asserted scope (the Chinese version states the classification as an explicit iff). The submission therefore targets the classification clause with a single, fully explicit dimension-4 counterexample — a valid disproof strategy for a universally quantified assertion, with no quantifier strengthening anywhere.

The counterexample is `K = [-1,1] × B₁³` in `ℝ⁴`, the octahedral prism. Lean proves it is a symmetric convex body (`K_body`: compact, convex, nonempty interior via an explicit open neighborhood of 0, centrally symmetric). The polar is *proved* by sign-testing against `(±1, ±eᵢ) ∈ K`: `K° = P = {y : |y₁| + maxᵢ|yᵢ| ≤ 1}` (`polar_K`), the ℓ∞-free-sum of the segment and cube — not the naive product of polars, which the submission correctly avoids. The volumes are genuinely computed by Lebesgue integration, not assumed: `volume_cross3` uses Mathlib's proved ℓₚ-ball formula (p = 1, n = 3 → 4/3); `volume_K = 8/3` by the product formula; `volume_P = 4` by slicing — section at `t` is the cube of side `2(1−|t|)`, and `∫₋₁¹ 8(1−|t|)³ dt = 16∫₀¹(1−t)³ dt = 4` is evaluated via the fundamental calculus lemma chain (`slice_integral`). Hence `M(K) = (8/3)·4 = 32/3 = 4⁴/4!`: K **attains** the conjectured bound.

The exclusion of both equality classes is by extreme-point counting: Lean proves `ext(B₁ⁿ)` = signed coordinate vectors (via the convex-hull characterization `cross_eq_hull_axes` and the extremality lemma `axis_extreme`), `ext([-1,1]) = {±1}`, product rule `extremePoints_prod`, giving `|ext K| = 12` vs `|ext C₄| = 16` and `|ext B₁⁴| = 8`. Since a linear equivalence maps extreme points bijectively, K is neither image; and any linear `f` with `f''Cube = K` is proved surjective (the range contains K, hence has nonempty interior) hence bijective in finite dimension, so singular maps are covered as well (`bijective_of_image_K`, `not_linear_image_Cube`, `not_linear_image_Cross`). The counterexample satisfies every stated hypothesis of the classification clause, so the clause is false; negating this conjunct falsifies the conjecture as printed (both the English implication reading and the stronger Chinese biconditional reading are negated). The report is appropriately explicit that this does not resolve the Mahler lower-bound problem itself.

I verified the mathematics independently: vol B₁³ = 2³/3! = 4/3; vol P = ∫₋₁¹ 8(1−|t|)³ dt = 4; product 256/24 = 32/3; extreme-point counts 12/16/8; the Python face-lattice computation corroborates all of these exactly.

## Issues found
- None blocking. The disproof addresses only the equality-classification clause, which is one of the two conjuncts the source asserts; the report and README disclose this scope precisely.

## Verdict
APPROVED. Fresh LaTeX and Lean builds pass; axioms are exactly the standard three; the exact-arithmetic auxiliary computation reproduces byte-for-byte and corroborates every geometric quantity; and the Lean counterexample — proved body, proved polar, proved volumes, proved non-image of both classes — decisively falsifies the equality classification asserted without dimensional restriction in the official bilingual statement.
