# Counterexample to 00000008905

The actual six-vertex simple graphs G=K1,4 plus one isolated vertex and H=C4 plus two isolated vertices have the same adjacency characteristic polynomial X^4(X^2-4), hence identical complex eigenvalues with all multiplicities. Nevertheless, their actual graph-homomorphism counts from the three-vertex path are respectively 20 and 16. No function of the eigenvalue multiset can reconstruct those counts.

The Lean proof constructs the actual SimpleGraph objects and adjacency matrices, proves characteristic-polynomial equality by an explicit invertible rational intertwiner, transports equality to complex coefficients and root multisets, and counts the complete types of SimpleGraph.Hom maps through an explicit equivalence. This is not a table of assumed graph invariants. Homomorphisms may identify the two endpoints of the path, as required by the usual definition.

The terse source is addressed under its standard graph-homomorphism spectral-reconstruction interpretation. It states no regularity restriction. The result does not dispute that adjacency spectra determine closed-walk counts.

## Reproduce

With Lean 4.19.0, run `lake update`, `lake exe cache get`, then `lake build` in `lean/`. Mathlib is pinned to c44e0c8ee63ca166450922a373c7409c5d26b00b. Public Git configuration is included; ignored local dependency junctions are not submitted.

Compile `report.tex` with a LaTeX engine supporting its standard packages. The included PDF was generated with Tectonic. See `VERIFICATION.md` for validation details.
