# Disproof of conjecture 00000007718

For each integer `m ≥ 1`, consider the actual three-letter substitution

\[
 a\mapsto a^{m+2}b^m c^{m+1},\qquad
 b\mapsto a^m b^{m+3}c^m,\qquad
 c\mapsto a^{m+1}b^m c^{m+2}.
\]

Every letter occurs in every substituted word. The substitution is primitive, has constant length `3m+3`, and subdivides each expanded colored unit interval into adjacent unit intervals. Its actual incidence matrix has complete complex spectrum `3m+3, 3, 1`, so the second-to-Perron ratio is `1/(m+1)`.

At `m=2`, the ratio is exactly `1/3 < (3-√5)/2`. This disproves the explicit positive-minimum clause in both language versions, and therefore their stated conjunction. In fact, these positive ratios become arbitrarily small, so there is no positive universal lower bound.

## Reproduction

`main.tex` and `main.pdf` give the mathematical argument. `conjecture.md` is the exact bilingual source. The complete project in `lean/` pins Lean 4.19.0 and Mathlib v4.19.0; `lake-manifest.json` fixes all nine dependency revisions.

From `lean/`, with the pinned Lean toolchain installed:

```sh
lake exe cache get
lake build
lake env lean -DwarningAsError=true Conjecture7718/Substitution.lean
lake env lean -DwarningAsError=true Conjecture7718/Tiling.lean
lake env lean -DwarningAsError=true Conjecture7718/Spectrum.lean
lake env lean -DwarningAsError=true Conjecture7718.lean
lake env lean -DwarningAsError=true Check.lean
```

The default build imports every implementation module. `Check.lean` prints all 21 definitions/abbreviations and the types and transitive axiom dependencies of all 43 theorems. There are no additional named or anonymous proof instances. No auxiliary numerical, simulation or symbolic program supplies any mathematical step. Rebuild the report with `tectonic main.tex`.

## Correspondence with the source

- `Substitution.lean` defines actual finite words by concatenation and repetition. The incidence matrix is the complexification of their natural-number letter counts. It proves the counts, constant length, nonempty words, word-iteration primitivity, positivity of matrix power one, and symmetry under either transpose convention.
- `Tiling.lean` uses the actual letters as colors on adjacent closed unit intervals. It proves exact support coverage, pairwise disjoint interiors, translation from the correctly colored unit prototiles, expansion by `3m+3`, and equality of the geometric color counts with the incidence counts.
- `Spectrum.lean` factors the actual characteristic polynomial and the determinant of the actual resolvent. It proves the complete complex spectrum, full matrix rank three, an actual positive Perron eigenvector, and the greatest modulus both before and after removing the Perron value.
- `Conjecture7718.lean` packages strictly ordered positive spectral data together with the characteristic polynomial and actual spectrum. `AdmissibleRatio` quantifies over primitive, nonempty, three-letter interval substitutions with full-rank matrices and this spectral certificate. Restricting to this subclass gives a necessary consequence of the source's universal minimum claim. `conjecture_00000007718_false` refutes that consequence using the certified example. `no_positive_universal_lower_bound` and `no_least_positive_admissible_ratio` give the stronger family result.

The source does not separately define `r`. Here `r=3` is the alphabet/matrix-size reading; the matrix also has actual rank three. No interpretation as ambient dimension or algebraic degree of the Perron value is silently imposed. The source contains no aperiodicity, unimodularity, characteristic-polynomial irreducibility, or substitution-length bound.

The formalization proves the finite geometric substitution rule and its matrix spectrum. It does not claim to construct a tiling hull, a two-sided fixed tiling, an invariant measure or pattern frequencies. These are unnecessary for refuting the explicit matrix-ratio minimum. The trace-error and algebraic-degree clauses are not separately settled.

`VERIFICATION.md` records the independent execution, matching report/PDF, eligibility and package checks. `SEMANTIC_REVIEW.md` records a separate source-level review by an agent who authored none of the proof or report. These are local validation and independent internal scrutiny; maintainer acceptance is a separate decision. `verification/SHA256SUMS.json` covers every submitted file except itself.
