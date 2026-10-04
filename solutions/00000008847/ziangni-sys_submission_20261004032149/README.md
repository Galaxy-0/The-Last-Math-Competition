# Proof of Conjecture 00000008847

Both assertions follow from a general theorem for pairwise graph
conditions: every admissible set-valued map has a maximal admissible
extension, and maximality of a map is equivalent to maximality of its
graph under inclusion. Source and target are arbitrary types, and the
compatibility predicate on pairs of graph points is arbitrary.

The submission formally specializes this theorem to both standard cases:

- Real normed-space operators into the continuous dual, with the actual
  monotonicity inequality `(u-v)(x-y) >= 0`. This includes Banach spaces.
- Real inner-product-space operators, with inequality
  `<x-y,u-v> >= 0`. This includes Hilbert spaces.

No completeness, full-domain, nonempty-domain, or operator-continuity
assumption is used. Empty values are allowed. A chain union preserves
pairwise compatibility; Zorn's lemma yields a maximal graph containing
the original graph. The graph/map inverse constructions transfer both
existence and maximality back to maps.

## Files

- `report.tex` and `report.pdf`: full general proof and standard specializations.
- `lean/`: Lean 4.19.0 project with a pinned Mathlib dependency.
- `VERIFICATION.md`: exact scope, correspondence, and verification evidence.

## Reproduction

With the pinned toolchain installed, run from `lean`:

```sh
lake exe cache get
lake build
lake env lean Main.lean
```

The manifest uses public Git revisions and no local paths. Local cache
links and build products are ignored. Use a short checkout path on
Windows to avoid path-length failures in Mathlib imports.

Compile the report from this submission directory with:

```sh
tectonic -X compile report.tex
```

The general final theorem is
`MaximalMonotone8847.conjecture_00000008847`. Its two checked standard
instances are `MaximalMonotone8847.InnerProduct.result` and
`MaximalMonotone8847.Duality.result`. The dual instance uses actual
continuous real linear functionals, not an assumed abstract value table.
Classical choice enters through Zorn's lemma. The theorem asserts
existence, not uniqueness or an effective extension-selection algorithm.
