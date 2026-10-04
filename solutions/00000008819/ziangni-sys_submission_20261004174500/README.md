# Disproof of conjecture 00000008819

The explicit claim that all closed proper convex objectives lie in the forward-backward convergence domain omits minimizer existence. On the real Hilbert line, f(x)=-x and g(x)=0 are actual proper closed convex functions. The actual gradient is constant -1, hence 1-Lipschitz and 1-cocoercive. Every genuine unit-step proximal subproblem has the unique solution y. The safe unit-step forward-backward iteration is therefore x+1, with iterates x+k from every start, and fails norm and weak convergence. The objective has no minimizer. The other source clauses are unused.

Lean proves the actual gradient, closed epigraphs, convexity, finite-valued properness, complete proximal minimizer relation, safe step, actual iterations, nonattainment, and full nonconvergence.

Reproduce in lean/ with Lean 4.19.0:

```text
lake update
lake exe cache get
lake build
```

Mathlib is pinned to c44e0c8ee63ca166450922a373c7409c5d26b00b. The build prints theorem axiom audits. No admitted proofs, custom axioms or native decision procedures are used.

The report is disproof.tex/disproof.pdf. Native compilation returned the known platform-directory failure; existing Tectonic compiled the PDF, whose two rendered pages were visually inspected.
