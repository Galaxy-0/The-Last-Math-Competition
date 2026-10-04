# Counterexample to conjecture 00000007152

Two actual real symmetric 3-by-3 matrices attain equality in the largest-eigenvalue Weyl bound but have no common eigenbasis.

Lean defines the matrices, actual eigenvalues through nonzero eigenvectors, and largest eigenvalues through universal eigenvalue bounds. It proves the bounds by quadratic forms, then proves that a common Basis of eigenvectors would force commutation, contradicted by direct matrix action.

The exact equality addressed is lambda_max(A+B)=lambda_max(A)+lambda_max(B). No simultaneous equality in every Weyl bound is claimed.

## Reproduction

Lean 4.19.0 with pinned Mathlib:

    cd lean
    lake update
    lake exe cache get Mathlib/Data/Matrix/Notation.lean Mathlib/Data/Real/Basic.lean Mathlib/LinearAlgebra/Matrix/ToLin.lean Mathlib/Tactic/FinCases.lean Mathlib/Tactic/Linarith.lean Mathlib/Tactic/NormNum.lean Mathlib/Tactic/Ring.lean
    lake build
    lake env lean Main.lean

Compile report.tex with Tectonic. See VERIFICATION.md.
