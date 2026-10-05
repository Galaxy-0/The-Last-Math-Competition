# Solution Review — Conjecture 00000006430 (PR 556)

**Submission:** ziangni-sys — `ziangni-sys_submission_20261004200200`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-04

## Checklist results
- Official bilingual conjecture read in full from `conjectures/00000006430.md`. It is an existential claim: two lattice sets with the same product-count conversion but different counting polynomials, realized by an explicit pair with the same sum count and different coefficients (存在…显式格点对). No SOURCE.md shipped.
- LaTeX `report.tex` read in full; rebuilt independently with `latexmk -pdf` (pdflatex): compiles cleanly. pypdf text comparison: exact match after NFKC normalization (the only raw difference is the "ﬀ" ligature glyph in the Tectonic-built PDF, an extraction artifact, not a content difference).
- Fresh `lake build` on Lean v4.19.0, Mathlib pinned at c44e0c8e: **Build completed successfully**, 1487 targets, zero errors, zero warnings.
- Axiom audit: 11 `#print axioms` lines, all `[propext, Classical.choice, Quot.sound]` only.
- Grep for `sorry`, `native_decide`, `axiom` declarations, `unsafe`, `@[implemented_by]`, `extern`, `admit`: no hits (only the VERIFICATION.md sentence asserting their absence).
- Auxiliary code: none included; all numerical claims independently recomputed in python instead — every one checks out (see below).
- `metadata.csv` on main marks 00000006430 neither proven nor disproven (unsolved).

## Semantic audit
The conjecture asserts the existence of two lattice sets separating the "conversion" layer (product/sum counts) from the "counting polynomial" layer, via an explicit pair with the same sum count and different coefficients. The submission proves exactly this: A = [0,1]×[0,8]×[0,12]∩ℤ³ and B = [0,2]×[0,2]×[0,25]∩ℤ³. Both have (1+1)(8+1)(12+1) = 234 = (2+1)(2+1)(25+1) points; hence |A×A| = |B×B| = 234² = 54756; both Minkowski self-sums are boxes with side lengths doubled, giving |A+A| = 3·17·25 = 1275 = 5·5·51 = |B+B| (the set identity F+F = F(2a,2b,2c) is proved via an honest coordinate-splitting argument, min(j,a) + (j − min(j,a))); and both normalized doubling constants equal 1275/234 = 425/78. Yet their Ehrhart polynomials differ: E_A(t) = (t+1)(8t+1)(12t+1) = 96t³+116t²+21t+1 versus E_B(t) = (2t+1)²(25t+1) = 100t³+104t²+29t+1, with different leading coefficients 96 ≠ 100 and difference 4t(t−1)(t−2), so they agree at t = 0,1,2 (input, and the sum count at t=2) and separate at t = 3 (3700 vs 3724). I recomputed all of these numerically in python (sympy expansions and box counts at t = 0,…,4): all confirmed.

The formalization is faithful and does not weaken the existential statement. `box` is an actual `Finset` of integer triples; `actual_sumset` proves a genuine Finset Minkowski identity; `K` is a real compact convex box in ℝ³ (`actual_compact`, `actual_convex`); `actual_lattice_points` proves membership of enumerated integer points is equivalent to membership in the actual scalar dilation t•K for every natural t, including the degenerate t = 0 case; `actual_ehrhart` proves the rational polynomial's evaluation equals the true lattice-point count `(box (t*m) (t*n) (t*p)).card` for every t — this is the honest Ehrhart statement, established by direct counting rather than by assuming polynomiality. The separation is packaged in `separation : countData A = countData B ∧ ehrhart 1 8 12 ≠ ehrhart 2 2 25`, plus `different_leading_coefficients` (96 vs 100) for the "different coefficients" clause. Notably, `every_count_conversion` proves that *every* function of the shared count tuple (cardinality, product count, sum count) takes the same value on A and B — the strongest possible reading of "same product-count conversion," so the result is robust against any reasonable interpretation of the vague official term. The quantifier structure (existence) matches the official bilingual text, and the explicit pair realizes it.

The report and Lean agree claim-by-claim, and the report's honest note that the source does not define any conversion beyond the count data is a fair treatment of the vague definition.

## Issues found
None blocking. (Only cross-engine PDF ligature extraction artifact, content identical after normalization.)

## Verdict
APPROVED. The submission proves the conjecture's existential claim with an explicit, fully formalized lattice pair: identical cardinality, product, sum and doubling-constant data, provably different Ehrhart counting polynomials with different leading coefficients. All mechanical checks pass, and every numerical claim was independently re-verified.
