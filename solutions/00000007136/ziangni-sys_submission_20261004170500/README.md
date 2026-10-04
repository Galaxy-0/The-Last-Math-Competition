# Counterexample to 00000007136

The full-dimensional Euclidean squares K=[0,1]^2 and L=[0,2]^2 have genuine Minkowski area polynomial area(sK+tL)=(s+2t)^2 for every s,t≥0. Their mixed areas are 1,2,4, so Alexandrov–Fenchel equality holds. Yet no ambient Euclidean isometry maps K onto L: every squared distance in K is at most 2, whereas L contains a pair at squared distance 8.

This refutes the source's congruence equality classification, not the Alexandrov–Fenchel inequality. The examples are homothetic; the source does not normalize volumes or identify bodies up to dilation.

The Lean project proves the actual set identity, Lebesgue area polynomial and polarization value; compactness, convexity and nonempty interior; transport to genuine EuclideanSpace with volume preservation; and noncongruence quantified over all ambient IsometryEquiv maps.

## Reproduce

With Lean 4.19.0, run `lake update`, `lake exe cache get`, then `lake build` in `lean/`. Mathlib is pinned to c44e0c8ee63ca166450922a373c7409c5d26b00b. Public Git configuration is included; ignored local dependency junctions are not submitted.

Compile `report.tex` with a LaTeX engine supporting its standard packages. The included PDF was generated with Tectonic. See `VERIFICATION.md` for validation details.
