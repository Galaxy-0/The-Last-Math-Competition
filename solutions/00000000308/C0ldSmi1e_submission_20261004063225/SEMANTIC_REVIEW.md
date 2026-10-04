# Internal semantic review

This is an internal submission audit, not an official competition review.

Both language versions assert empty intersection with every real line and describe bad approximation informally. The submission makes its standard-definition interpretation explicit and cites primary literature for the criterion with a positive constant and the squared complex denominator modulus. No cited theorem is inserted as an unproved premise.

1. **Actual approximation set.** `BadC` is exactly the set of complex `z` for which some real `c > 0` gives `c / ‖(q : ℂ)‖^2 ≤ ‖z - (p : ℂ)/(q : ℂ)‖` for every `p q : GaussianInt`, `q ≠ 0`. The casts occur before division, so this is complex division, not Gaussian Euclidean division.
2. **Real estimate.** The bound covers arbitrary signed integers `m,n` with only `m ≠ 0`. Irrationality of `sqrt(2)` proves the integer `2*m^2 - n^2` is nonzero. Its absolute value is at least one; the conjugate-factor argument proves the explicit constant `1/4` uniformly.
3. **All Gaussian denominators.** A nonzero Gaussian integer has a nonzero real or imaginary integer coordinate. Both cases are covered. Coordinate absolute values are bounded by complex norms, giving the lower bound for the full complex linear error. Faithfulness of `GaussianInt.toComplex` establishes the denominator's nonzero complex value and positive norm before division.
4. **Actual real line.** `realLine a v` is the set of points `a + t*v`, `t : ℝ`, with `v ≠ 0` required in the conjectured universal claim. The chosen direction is `1`, not zero. The selected line is proved equal to the range of the real embedding into the complex numbers.
5. **Explicit counterexample and complete negation.** `sqrt_two_mem_BadC` and `sqrt_two_mem_realAxis` supply the same point. The final theorem negates the entire universal empty-intersection clause by specializing to the real axis. No finite test or restricted denominator class replaces a quantifier.
6. **Scope.** The first conjunct is disproved under the standard definition. The separate complement-measure and rate clauses are not formalized or claimed false. The witness works for both affine real lines and real linear lines through zero.
7. **Trust.** No admissions, new axioms, unsafe declarations, native evaluation shortcuts, or altered kernel-check settings occur in the submitted proof sources. Eight central results have their axiom dependencies printed in the included audit.

An independent agent read all four proof modules and the audit file, checked the relevant Gaussian embedding APIs and source definitions, and found no mathematical or semantic blocker. Its source audit was separate from the submitting agent's fresh project build and direct source replay.
