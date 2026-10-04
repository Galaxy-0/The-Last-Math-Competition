# Disproof of conjecture 00000003474

For the original single-variable (vertex-nullity) interlace polynomial,
the disjoint union of two five-vertex paths has

`q(P5 disjoint-union P5; x) = x^2 (x^2 + 5x + 2)^2`.

Thus `(-5 - sqrt(17))/2 < -4` is a repeated real root, contradicting the
first clause. Both source languages leave the graph class unrestricted;
neither imposes connectedness or specifies another interlace variant.

## Contents and reproduction

- `main.tex` and `main.pdf`: short complete mathematical proof and scope.
- `SOURCE.md`: byte-exact bilingual conjecture; provenance is in
  `verification/SOURCE_PROVENANCE.md`.
- `lean/Main.lean`: actual graph/pivot/delete computation and root-location disproof.
- `verify.py`: independent exact GF(2) subset-nullity enumeration.
- `verification/BUILD.json` and logs: fresh-build and PDF results.
- `verification/SELF_REVIEW.md`: adversarial self-review and boundaries.

Using Lean 4.19.0 and the commit-pinned public dependencies:

```text
cd lean
lake exe cache get
lake build
lake env lean -DwarningAsError=true Main.lean
```

The included manifest records every dependency's Git commit. The standard
Mathlib cache command is optional when dependencies are already built.
Run `python verify.py` from the package root. The Python script uses only
the standard library. Compile `main.tex` with Tectonic or a compatible LaTeX
installation.

## Formal result and boundary

`Conjecture3474.conjecture_false` negates the universal real repeated-root
location clause. The witness is a genuine loopless symmetric adjacency
matrix on ten vertices, not a polynomial asserted to represent an unknown
graph. `interlace_eq_leaf_sum` proves that the auxiliary finite computation
implements the polynomial pivot recurrence. The square linear divisor is
proved over the real numbers, and the polynomial is proved nonzero.

The standard equivalence of this original pivot definition with the
vertex-nullity formula, and general independence of pivot order, are cited
published mathematics rather than additional newly formalized theorems.
No imported hypothesis supplies the graph's polynomial. The first-clause
counterexample suffices; no claim is made about the source's other clauses
or about other interlace polynomial variants.

Final/core theorem axiom reports use only `propext`, `Classical.choice`, and
`Quot.sound`; graph simplicity checks use none. No `sorry`, `admit`,
`native_decide`, or custom axiom is used.
