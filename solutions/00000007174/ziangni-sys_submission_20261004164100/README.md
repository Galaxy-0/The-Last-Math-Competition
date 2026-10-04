# Disproof of 00000007174

The actual invertible normal real matrix [[0,-2],[2,0]] has Euclidean operator norm2 and inverse norm1/2. Its spectral2-norm condition number is1, but its actual antisymmetric part (A-A*)/2 equalsA and has norm2. Thus the alleged lower-bound inequality fails. Its actual complexified eigenvalues are precisely±2i, with equal moduli, so the eigenvalue-modulus ratio is also1.

Lean models the real Euclidean plane as the actual real Hilbert space C, with genuine real continuous linear maps A(z)=2iz and B(z)=-iz/2. It verifies the real coordinate matrix, both inverse identities, actual operator norms, actual adjoint, normality and the lower-bound failure. It separately computes the determinant of the complexified matrix and its complete zero set and eigenvalue moduli. The complex norm is Euclidean, not the coordinate sup norm.

Reproduce from lean/ using Lean4.19.0:

```text
lake update
lake exe cache get
lake build
```

Mathlib is pinned to c44e0c8ee63ca166450922a373c7409c5d26b00b. Full build prints final axiom audits. No admitted proofs, custom axioms or native decision procedures.

The full report is disproof.tex/disproof.pdf. Native compilation was attempted and returned its known platform-directory failure. Existing Tectonic compiled the one-page PDF, which was rendered and visually checked with no clipping or overflow. Both normalized and unnormalized antisymmetric conventions are explained.
