# Proof of conjecture 00000006837

For every bounded operator on a real or complex Hilbert space, an invariant linear subspace has an adjoint-invariant orthogonal complement. For closed subspaces this is an equivalence, and orthogonal complementation gives an order-reversing bijection between the two closed invariant-subspace lattices.

Lean uses actual continuous linear operators, adjoints and submodule orthogonal complements. The arbitrary-subspace direction is proved separately; the converse explicitly requires closedness because the double complement equals the closure.

## Reproduction

With Lean 4.19.0 and the pinned Mathlib revision:

    cd lean
    lake update
    lake exe cache get Mathlib/Analysis/InnerProductSpace/Adjoint.lean
    lake build
    lake env lean Main.lean -DwarningAsError=true

Compile report.tex with Tectonic. See VERIFICATION.md for observed validation.
