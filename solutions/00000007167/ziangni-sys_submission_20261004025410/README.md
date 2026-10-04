# Disproof of conjecture 00000007167

For the identity operator on the complex Hilbert line, the actual operator norm and numerical radius both equal 1. Their ratio is 1, contradicting the asserted upper bound of 1/2.

The Lean model uses Mathlib's bounded complex-linear identity and its standard operator norm. It defines numerical radius as the supremum of the actual unit-vector inner-product values and proves the entire value set is the singleton {1}. No spectral proxy or asserted radius is used.

## Reproduction

Lean 4.19.0 and the pinned Mathlib manifest:

    cd lean
    lake update
    lake exe cache get Mathlib/Analysis/InnerProductSpace/Basic.lean Mathlib/Analysis/NormedSpace/OperatorNorm/NormedSpace.lean Mathlib/Order/ConditionallyCompleteLattice/Basic.lean Mathlib/Tactic/NormNum.lean
    lake build
    lake env lean Main.lean

Compile report.tex using Tectonic. Verification results appear in VERIFICATION.md.
