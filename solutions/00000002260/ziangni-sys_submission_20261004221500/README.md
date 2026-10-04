# An entire function of order five exceeds the planar bound

Conjecture 00000002260 imposes no order restriction on its lower bound dim_H J(f) >= rho/2. The actual entire function f(z)=exp(z^5) has genuine closed-disk maximum modulus exp(r^5), attained on the boundary at real r. Its logarithmic growth quotient equals5 for every r>1, so its actual limsup order is5. Every subset of the complex plane has Hausdorff dimension <=2, hence no such subset can satisfy the stated lower bound5/2. This universal theorem applies directly to the genuine Julia set without substituting an invented set or computing its dynamics.

Lean verifies actual differentiability, the supremum and maximum-modulus identity, the logarithmic growth limit and actual limsup order, the ambient Hausdorff theorem and the universal contradiction. Hausdorff dimensions are handled as ENNReal with a finite upper bound.

Reproduce in lean/ using Lean4.19.0:

```text
lake update
lake exe cache get
lake build
```

Mathlib is pinned to c44e0c8ee63ca166450922a373c7409c5d26b00b. The full build prints five standard-only theorem axiom audits. No admitted proofs, custom axioms or native decision procedures.

Complete report: proof.tex/proof.pdf. Existing Tectonic compiled the two-page PDF; both rendered pages were visually checked. Native compilation returned the known platform-directory failure.
