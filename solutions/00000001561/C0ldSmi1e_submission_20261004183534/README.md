# Disproof of conjecture 00000001561

Every oriented closed hemisphere of the actual unit sphere contains two antipodal equatorial points. Their spherical distance is pi, so the hemisphere fails the source's pairwise bound of pi/2 and cannot be an admissible area-maximizer.

There is also an interior counterexample for every orientation: with perpendicular unit vectors v,w, the points `(3/5)v+(4/5)w` and `(3/5)v-(4/5)w` are unit vectors strictly inside the hemisphere. Their mutual inner product is `-7/25`, so their great-circle distance exceeds pi/2. Even deleting the entire equator does not repair the claimed extremizer.

The exact bilingual source is included as `conjecture.md`. The formal target negates its necessary first extremizer clause. No interpretation or computation of the unspecified second-extremizer clause is needed, and no theorem about arbitrary almost-everywhere modifications of a hemisphere is claimed.

## Reproduce the Lean verification

Lean 4.19.0 and Mathlib v4.19.0 are pinned, with all nine dependency revisions locked in the manifest. From `lean/`, after installing the pinned toolchain and fetching the pinned dependencies:

```sh
lake exe cache get
lake build
lake env lean -DwarningAsError=true Conjecture1561/Definitions.lean
lake env lean -DwarningAsError=true Conjecture1561/Boundary.lean
lake env lean -DwarningAsError=true Conjecture1561/Interior.lean
lake env lean -DwarningAsError=true Conjecture1561.lean
lake env lean -DwarningAsError=true Check.lean
```

`Check.lean` prints all 12 definitions/abbreviations and checks the types and transitive axiom dependencies of all 21 named theorems. The allowed axioms are only the usual `propext`, `Classical.choice`, and `Quot.sound`. There are no admitted proofs, custom axioms, native decision proofs, or auxiliary numerical computations.

## Actual objects and scope

- The ambient space is `EuclideanSpace ℝ (Fin 3)` with its Euclidean norm, not a coordinate function space with the default sup norm.
- The sphere is `Metric.sphere 0 1`; spherical distance is `InnerProductGeometry.angle`, explicitly proved equal to arccos of the inner product on unit vectors.
- Hemispheres are intersections with actual inner-product halfspaces. The perpendicular witness comes from an actual orthonormal basis of the pole's orthogonal complement.
- `Admissible` requires sphere membership and the distance bound for every pair. `IsAreaMaximizer` explicitly requires admissibility as well as comparison with every admissible competitor.
- The exclusion of hemisphere maximizers holds for every objective measure, and is specialized to actual two-dimensional Hausdorff measure. Its normalization is immaterial because feasibility already fails; no surface-area normalization identity or value is assumed.

## Contents

- `lean/Conjecture1561/Definitions.lean`: the actual sphere, distance, hemispheres, admissibility, measure-maximization predicate, and necessary first clause.
- `lean/Conjecture1561/Boundary.lean`: distance convention, perpendicular unit vector, antipodal witness, and failure for every closed hemisphere.
- `lean/Conjecture1561/Interior.lean`: the two actual interior points, their norms and inner products, and the strict distance violation.
- `lean/Conjecture1561.lean`: every open hemisphere fails too; neither kind can maximize for any measure; `conjecture_false` negates the first clause with actual Hausdorff measure.
- `main.tex` and `main.pdf`: matching report. Standard LaTeX packages only; compile with `pdflatex main.tex` twice or `tectonic main.tex`.
- `VERIFICATION.md`, `SEMANTIC_REVIEW.md`, and `verification/`: exact execution, identity, eligibility, and independent internal review records.

The execution records distinguish a fresh project build using a pinned dependency cache from rebuilding all dependencies. Local validation and internal review are distinct from official maintainer acceptance.
