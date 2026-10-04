# Disproof of conjecture 00000008590

In a fixed 3×3 scalar-block layout, specify all entries zero except the central entry (1,1). Zero is the unique norm-minimizing positive completion and the unique Loewner-minimal positive completion, although the missing block is not a corner. This refutes the necessity direction of the source's corner uniqueness assertion under both standard interpretations of minimality.

Lean uses actual continuous linear operators on the real Euclidean Hilbert space of dimension 3, actual entries in its standard orthonormal basis, genuine operator norms, positivity and self-adjointness expressed by inner products, and actual Loewner comparison of quadratic forms. The proof includes polarization establishing that a positive operator below zero is zero. The report uses the fixed matrix layout; neither source imposes nondegeneracy of the specified entries.

Reproduce from lean/ with Lean 4.19.0:

```text
lake update
lake exe cache get
lake build
```

Mathlib is pinned to c44e0c8ee63ca166450922a373c7409c5d26b00b. Ignored local package junctions only reuse the cache. The full build prints six axiom audits. No admitted proofs, custom axioms or native decision procedures are used.

The built-in LaTeX editor/compiler was attempted and encountered its platform-directory failure. Existing Tectonic produced the one-page PDF, which was rendered and visually inspected. The report's additional description diag(0,t,0), t≥0, is elementary and unnecessary for the formalized counterexample.