# Exact Bregman splitting without an attained solution

Conjecture 00000008836 states unconditional Bregman splitting convergence. On the real Hilbert line, f(x)=-x and mirror h(x)=x²/2 are proper closed convex functions. The actual Bregman distance is (y-x)²/2. Every genuine unit-penalty proximal subproblem has the unique global minimizer x+1, its true subgradient satisfies the exact Bregman inclusion, and the relative-error residual is zero. All-start iterates x0+k fail norm and weak convergence. The missing minimizer/zero hypothesis is explicit; the summability characterization is untouched.

Lean verifies the full definitions and all-competitor inequalities, actual gradients, Bregman geometry, maximal subgradient graph, complete argmin relation, relative-error certificate, iterates and nonconvergence.

Reproduce in lean/ using Lean 4.19.0:

```text
lake update
lake exe cache get
lake build
```

Mathlib is pinned to c44e0c8ee63ca166450922a373c7409c5d26b00b. The build prints theorem axiom audits. No admitted proofs, custom axioms or native decision procedures.

The report is proof.tex/proof.pdf. Existing Tectonic compiled the two-page PDF; both rendered pages were visually checked without overflow/clipping. The native compiler returned its known platform-directory failure.
