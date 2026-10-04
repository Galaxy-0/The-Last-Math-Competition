# Counterexample to conjecture 00000007177

For the actual symmetric positive definite matrices A=diag(1,2) and B=[[2,1],[1,3]], the pencil has generalized eigenvalue 1 with eigenvector (1,-1). This value cannot be a quotient of any eigenvalue of A by any eigenvalue of B.

Lean proves positivity of both quadratic forms, the actual pencil eigenvector equation, the complete spectrum characterization of A, and exclusion of 1 and 2 from B's spectrum. It therefore excludes every possible individual-spectral quotient representing 1.

The claim targeted is a quotient of the individual spectra. The valid generalized Rayleigh quotient using the same vector in both quadratic forms is a different quantity and is not disputed. The source's separate extremum clause is not needed for this disproof.

## Reproduction

Lean 4.19.0 with pinned Mathlib:

    cd lean
    lake update
    lake exe cache get Mathlib/Data/Matrix/Notation.lean Mathlib/Data/Real/Basic.lean Mathlib/Tactic/FinCases.lean Mathlib/Tactic/Linarith.lean Mathlib/Tactic/NormNum.lean
    lake build
    lake env lean Main.lean

Compile report.tex with Tectonic. See VERIFICATION.md.
