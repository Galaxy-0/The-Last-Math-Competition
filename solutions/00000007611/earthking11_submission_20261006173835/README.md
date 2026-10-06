# Disproof of conjecture 00000007611

This submission refutes the natural interpretation that every system of (n)
real gamma matrices satisfying the Euclidean Clifford relations must have
matrix size at least (2n). In dimension (n=2), the two real (2\times2)
matrices in `main.tex` square to the identity and anticommute, so a size-2
system exists while the proposed bound would require size at least 4.

The conjecture does not define the coefficient field, the dimension being
bounded, or the phrase “tightness of the trace identity.” Accordingly, this
submission establishes a counterexample to the stated lower-bound reading;
it does not claim to settle the other unformalized clauses. If a different
meaning of “dimension” was intended, the conjecture needs to specify it.

The Lean 4 project defines the matrices entrywise and verifies both square
identities, anticommutation, and (2<2\cdot2).

Verification, from this directory:

```text
cd lean4
lake build
lake env lean Check.lean
```

The project uses only core Lean and has no `sorry`, `native_decide`, or added
axioms.
