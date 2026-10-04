# Identical central sections of noncongruent intervals

Conjecture 00000007809 allows dimension one. The actual compact convex intervals [-1,1] and [-2,2] contain a common symmetric neighborhood of zero. Every unit direction has genuine orthogonal subspace {0}. Intrinsic zero-dimensional Lebesgue volume, transported through an actual linear isometric coordinate equivalence from Fin 0 → R, gives section volume one for both bodies. Their diameters 2 and 4 rule out congruence under every pair of isometries.

This disproves the unrestricted uniqueness clause in dimension one only. It makes no claim for dimensions >=2 and leaves the spherical-harmonic condition-number clause untouched. The section measure is intrinsic zero-dimensional volume, not ambient one-dimensional volume.

Reproduce from lean/ with Lean 4.19.0:

```text
lake update
lake exe cache get
lake build
```

Mathlib is pinned to c44e0c8ee63ca166450922a373c7409c5d26b00b. The full build prints theorem axiom audits. No admitted proofs, custom axioms or native decision procedures.

Complete report: proof.tex/proof.pdf. Native compilation returned the known platform-directory failure. Existing Tectonic compiled the one-page PDF, which was visually checked without overflow or clipping.
