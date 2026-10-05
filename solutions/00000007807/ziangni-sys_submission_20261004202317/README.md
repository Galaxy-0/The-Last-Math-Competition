# A convex interval has no positive boundary log-Sobolev constant

Conjecture 00000007807 includes dimension one. The actual convex body [-1,1] has zero-dimensional Hausdorff boundary measure equal to the sum of its endpoint Dirac measures. Its normalized probability measure has masses one half, and its surface-to-volume ratio is one.

The smooth cubic (2+3x-x^3)/4 has endpoint values zero and one and actual gradient zero at both endpoints. Its genuine entropy integral is log(2)/2 > 0, while its genuine Dirichlet energy is zero. Thus the actual set of admissible nonnegative log-Sobolev rate constants is {0}, whose supremum is zero. This refutes every positive universal lower bound in the unrestricted dimension-one case. Higher-dimensional, curvature and prism clauses are not separately assessed. Zero ambient gradient also gives zero intrinsic tangential gradient.

Reproduce inside lean/ with Lean 4.19.0:

```text
lake update
lake exe cache get
lake build
```

Mathlib is pinned to c44e0c8ee63ca166450922a373c7409c5d26b00b. The final full build prints eight theorem axiom audits. The report is proof.tex/proof.pdf; the two-page PDF was compiled with existing Tectonic and both pages were visually checked.
