# Disproof of 00000008487

The source simultaneously claims that locked functions form a dense G_delta set and that their complement is dense and open. These claims are incompatible in any nonempty topological space: density forces intersection with every nonempty open set, including the alleged open complement.

Lean proves the universal impossibility for every subset of every nonempty topological space, then specializes to the actual continuous-function space C([0,1],R), containing the zero observable. No locking convention can satisfy the conjunction; no replacement definition of locking or infinite-dimensional Lebesgue measure is imposed. The actual Dense, IsOpen and IsGδ predicates are used.

Reproduce from lean/ using Lean 4.19.0:

```text
lake update
lake exe cache get
lake build
```

Mathlib is pinned to c44e0c8ee63ca166450922a373c7409c5d26b00b. The final full build passes and prints four audits using only standard axioms. No admitted proofs, custom axioms or native decision procedures.

The complete report is disproof.tex/disproof.pdf. Native compilation was attempted and returned its known platform-directory failure. Existing Tectonic compiled the one-page PDF, rendered and visually checked with no overflow or clipping.
