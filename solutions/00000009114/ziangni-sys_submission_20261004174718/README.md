# Counterexample to 00000009114

Four actual open Euclidean disks of radius 11/10 centered at (1,0), (0,1), (-1,0), (0,-1) share the origin, and each center belongs only to its own disk. Every selected subfamily covering the four centers must therefore include all four disks. Its overlap multiplicity at the origin is four, exceeding dimension plus one, which is three.

This uses the standard given-family centered-ball selection formulation. It does not replace the supplied balls by smaller balls and does not concern fine-cover theorems with arbitrarily small replacement balls. The source gives an unrestricted multiplicity bound; the separate needle-shaped extremizer clause is not needed.

The Lean proof uses actual EuclideanSpace, Metric.ball sets, finrank, arbitrary selected subfamilies, and filtered-cardinality multiplicity. It verifies separation, the common point, covering existence, forced selection and the impossibility of every dimension-plus-one bounded subcover.

## Reproduce

With Lean 4.19.0, run `lake update`, `lake exe cache get`, then `lake build` in `lean/`. Mathlib is pinned to c44e0c8ee63ca166450922a373c7409c5d26b00b. Public Git configuration is included; ignored local dependency junctions are not submitted.

Compile `report.tex` with a LaTeX engine supporting its standard packages. The included PDF was generated with Tectonic. See `VERIFICATION.md` for validation details.
