# Disproof of conjecture 00000002208

The actual additive closure of {1,2} in the nonnegative rationals is atomic, but its integer span has rank 1. This refutes the necessity direction of the stated criterion. Rational generators also satisfy the source's positive-real convention through the usual embedding.

The full proof is in disproof.tex/disproof.pdf. Lean defines the actual generated additive submonoid, proves it equals the natural-number casts, establishes that zero is its only additive unit, proves 1 is an atom, and constructs a finite list of atoms summing to every monoid element. An explicit integer-linear equivalence with Z establishes Mathlib's actual Module.rank of the generator span as 1.

Reproduce from lean/ with Lean 4.19.0:

```text
lake update
lake exe cache get
lake build
```

Mathlib is pinned to c44e0c8ee63ca166450922a373c7409c5d26b00b. Local ignored package junctions only reuse the cache. The final full build prints six axiom audits, all using only propext, Classical.choice and Quot.sound. No admitted proofs, custom axioms or native decision procedures.

The built-in LaTeX editor/compiler was attempted; its platform-directory failure was bypassed with existing Tectonic. The final one-page PDF was rendered and visually inspected. No auxiliary computations are needed.