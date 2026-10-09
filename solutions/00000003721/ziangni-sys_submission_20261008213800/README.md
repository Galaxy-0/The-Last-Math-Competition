# Disproof of conjecture 00000003721

The connected star K1,3 retains eigenvalue one with multiplicity at least two for every unit-modulus edge-phase tuple. Two explicit independent eigenvectors certify this directly for the actual Hermitian magnetic Laplacian D−A_z. Hence no generic phase choice can remove all degeneracy.

The certificate constructs the genuine simple graph and its degrees, proves connectedness, verifies the phased Hermitian Laplacian, and proves a lower bound of two on its eigenvalue-one eigenspace dimension for every admissible tuple. The report explains the tree gauge mechanism and the absence of a tree or cycle-flux restriction in the source.

## Reproduce

Run `lake build` in `lean/` with Lean 4.19.0. Public Mathlib is pinned to c44e0c8ee63ca166450922a373c7409c5d26b00b; ignored cache junctions are local only.

The full build passed with standard-only final theorem axiom audits. Final PDF compiled with Tectonic, rendered with Poppler and visually checked.
