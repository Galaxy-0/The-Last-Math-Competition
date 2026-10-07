# Disproof of conjecture 00000007627

The source describes ideals as left-module structures and asserts, among other
things, that the count of minimal ideals is given by the center dimension. It
does not restrict the ring to a Clifford algebra, nor does it give a more
specific ring, field, or decomposition hypothesis. Accordingly, this submission
tests the stated general left-module claim on the explicit finite algebra
`R = M₂(F₂)`. It makes no claim that this example is a Clifford algebra.

Regard `R` as a left module over itself by left multiplication. `leftColumn0`
and `leftColumn1` are the actual `Submodule R R` consisting of matrices
supported in the first and second columns, respectively. The proof establishes
that both are nonzero minimal left ideals and that they are distinct. The type
`MinimalLeftIdeal` is the subtype of all minimal submodules of this left regular
module; its finiteness follows from finiteness of `R`, and an injection from
`Fin 2` proves its cardinality is at least two.

Mathlib's central-algebra result proves that the center of `M₂(F₂)` is exactly
the scalar copy of `F₂`; thus its center has vector-space dimension one over
`F₂`. The theorem `minimal_left_ideal_count_ne_center_dimension` combines these
facts to disprove the center-dimension counting clause with the actual algebra,
actual left ideals, and actual center. The construction does not substitute a
finite proxy for the ideals or the ring.

The first clause is also addressed directly: `matrixOneFactorDecomposition`
is the actual ring equivalence from `R` to a one-indexed product of copies of
the same matrix ring. Its index type is `Fin 1`, whose cardinality is one, while
the proved minimal-left-ideal count is at least two. Thus
`minimal_left_ideal_count_ne_matrix_factor_count` gives the concrete mismatch
for this direct-product decomposition.

The source does not provide a general definition of “matrix-factor count” or
“direct-sum index.” The one-factor comparison here uses an explicitly proved
ring equivalence and its actual index type, not a custom count function. This
formalization makes no broader claim about unspecified decomposition
conventions; it shows that both the center-dimension clause and the natural
one-factor decomposition instance of the minimal-ideal/matrix-factor equality
fail under the supplied general left-module wording.

Build and axiom audit details are in [`BUILD_AUDIT.md`](./BUILD_AUDIT.md).
