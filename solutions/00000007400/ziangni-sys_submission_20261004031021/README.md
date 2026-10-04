# Disproof of conjecture 00000007400

The purely odd complex line with zero action of the purely even one-dimensional abelian Lie superalgebra has superdimension 0 - 1 = -1.

The Lean project defines an actual direct grading by complex subspaces and a bilinear action satisfying the representation commutator identity and parity preservation. It constructs the zero-action witness, verifies the bracket laws, and computes the subspace dimensions using Mathlib finrank.

## Reproduction

Lean 4.19.0, pinned Mathlib:

    cd lean
    lake update
    lake exe cache get Mathlib/Analysis/Complex/Basic.lean Mathlib/LinearAlgebra/FiniteDimensional/Basic.lean Mathlib/LinearAlgebra/Dimension/Finrank.lean Mathlib/Tactic/NormNum.lean
    lake build
    lake env lean Main.lean

Compile report.tex with Tectonic. See VERIFICATION.md.
