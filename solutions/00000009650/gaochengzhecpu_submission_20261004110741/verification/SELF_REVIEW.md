# Solo adversarial review: conjecture 00000009650

Verdict: PASS for the same-matrix, distinct-eigenvalue inner-product definition
printed in both source languages. This is a separate adversarial self-review
by the same assistant; no independent or subagent review is claimed.

## Mathematical and semantic objections checked

1. The source explicitly defines the overlap as the squared inner product of
   eigenvectors for distinct eigenvalues, and explicitly names GOE/GUE. The
   proof uses the real symmetric class only, avoiding the ambiguity of a
   complex square and avoiding substitution of left/right nonnormal overlaps.
2. Orthogonality is derived from actual self-adjointness and actual eigenvector
   equations over real inner-product spaces, not assumed. The derivation needs
   only distinct eigenvalues; normalization is not needed for zero overlaps.
3. The empirical average is defined over the actual finite strict-upper index
   set. Its nonemptiness for n>=2 is proved before division. The point-mass
   theorem holds for every test function, not merely the identity test or an
   arbitrarily defined summary statistic.
4. The exact mean is zero while 2/n is strictly positive. A separate real-limit
   theorem treats any sequence of genuine normalized symmetric eigensystems,
   not just a fixed dimension. Uniqueness of real limits rules out convergence
   of n times the mean to 2, so the asymptotic-equivalence reading also fails.
5. Concrete diagonal operators exist in every dimension, with actual
   Euclidean standard vectors. Lean verifies symmetry, normalization, distinct
   eigenvalues and the eigenvector equations. The paper does not pretend that
   deterministic diagonal matrices themselves are GOE samples: the universal
   pointwise orthogonality theorem applies to GOE. GOE simplicity is explained
   by the nonzero discriminant polynomial and its absolutely continuous law.
6. The paper supplies the measure interpretation of the all-test-functions
   identity and the elementary singleton-mass obstruction to a density. It
   honestly states that Gaussian measures and the optional inclusive-diagonal
   convention are not formalized in this project. The formal contradiction is
   already the universal exact/asymptotic mean contradiction in the printed
   distinct-eigenvalue convention.
7. Including diagonal entries changes the mean to 2/(n+1) for normalized
   vectors, asymptotic to 2/n. This possible ambiguity is handled explicitly:
   the limiting measure is still delta_0, refuting the asserted density. The
   manuscript does not incorrectly use a zero-mean claim for inclusive diagonals.
8. The Bourgade-Dubach reference concerns nonnormal Ginibre eigenvectors. It is
   cited only to clarify the source's attribution; no claimed new theorem
   about that different overlap statistic appears in the submission.

## Actual checks

Lean 4.19.0 fresh-project build and direct Lean check passed with warnings as
errors. Seven printed final/core theorem dependencies are only propext,
Classical.choice and Quot.sound. No custom axiom, unfinished proof or
native_decide is used. Official Mathlib dependencies were reused at the exact
manifest commits with clean tracked sources, and this is recorded in BUILD.json.

The Python script passed exact rational checks in dimensions 2 through 12 and
a non-diagonal rational symmetric 2x2 example. It is only supplementary.

The LaTeX was compiled with existing Tectonic because the native compiler
reported its platform-directory error. Both final PDF pages were rendered and
visually checked: equations are legible, no clipping or overflow occurs, and
the complete proof, scope discussion and reference are present. No TeX warning.

## Remaining maintainer judgment

The conclusion concerns the literal same-matrix overlap definition. Replacing
it with a nonnormal left/right overlap or an independent-matrix eigenvector
statistic would be a changed problem. Acceptance remains the maintainer's decision.
