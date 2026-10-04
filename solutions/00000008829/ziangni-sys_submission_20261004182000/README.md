# Failure of unqualified finite active-set identification

For conjecture 00000008829, ordinary projected gradient minimizes the actual strongly convex objective x^2/2 on the closed convex ray x>=0. The unique solution is zero. A safe half step from1 yields the genuine iterates2^-k, which converge to the solution but remain strictly positive. Their actual indexed active set is empty at every finite step, whereas the solution's active set contains the sole constraint.

This disproves the source's unqualified finite-identification law under its universal interpretation for canonical optimization methods. The source specifies no algorithm or nondegeneracy assumptions. The report explicitly identifies failure of strict complementarity and does not claim that every possible algorithm fails. Other source clauses are untouched.

Lean verifies the actual objective/gradient, convexity and closed epigraph, quadratic strong-convexity identity, unique constrained minimizer, actual metric projection inequality, projected-gradient update and all iterates, convergence, indexed active sets and quantified failure of eventual identification.

Reproduce from lean/ with Lean4.19.0:

```text
lake update
lake exe cache get
lake build
```

Mathlib is pinned to c44e0c8ee63ca166450922a373c7409c5d26b00b. Full build prints theorem axiom audits. No admitted proofs, custom axioms or native decision procedures are used.

The full report is disproof.tex/disproof.pdf. Native compilation returned the known platform-directory failure; existing Tectonic compiled the one-page PDF. Its full rendered page was visually inspected without clipping or overflow.
