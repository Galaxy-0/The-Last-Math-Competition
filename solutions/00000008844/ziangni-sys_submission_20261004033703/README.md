# Proof of conjecture 00000008844

For a monotone set-valued operator on a real Hilbert space and a positive resolvent parameter, its resolvent is firmly nonexpansive on its natural domain, and its fixed points are exactly the operator's zeros.

The proof works on any real inner-product space; completeness is unnecessary. Lean defines the actual inverse graph of I + lambda A, proves uniqueness, constructs the map on the graph's range, and verifies both claimed properties. No existence or totality outside the natural domain is assumed.

## Reproduction

Lean 4.19.0 with the pinned Mathlib revision:

    cd lean
    lake update
    lake exe cache get Mathlib/Analysis/InnerProductSpace/Basic.lean Mathlib/Tactic/Linarith.lean Mathlib/Tactic/Ring.lean
    lake build
    lake env lean Main.lean

Compile report.tex with Tectonic. See VERIFICATION.md for observed checks.
