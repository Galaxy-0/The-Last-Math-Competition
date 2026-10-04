# Disproof of unqualified two-block ADMM convergence

Conjecture00000008838 omits feasibility. Scalar strongly convex blocks f=g=x²/2 and actual nonzero continuous linear couplings A x=(x,0),B y=(y,0) into the real Euclidean plane, with c=(0,1), define an infeasible problem. Every actual unit-penalty ADMM augmented-Lagrangian subproblem has a unique global minimizer at every state. Starting from zero, the full actual trajectory has primal x=y=0 and scaled dualu=(0,-k). The dual fails norm and weak convergence; the primal is stationary but infeasible, with residual(0,-1). The three-block clause is untouched.

Lean verifies the true Euclidean augmented Lagrangian, actual CLMs and block objective properties, unique global subproblem minimizers via exact squared-gap identities, all full-state iterates and residuals, and actual dual nonconvergence via the second-coordinate continuous linear functional.

Reproduce from lean/ with Lean4.19.0:

```text
lake update
lake exe cache get
lake build
```

Mathlib is pinned to c44e0c8ee63ca166450922a373c7409c5d26b00b. The full build prints theorem axiom audits. No admitted proofs, custom axioms or native decision procedures are used.

Complete report: disproof.tex/disproof.pdf. Native compilation returned the known platform-directory failure. Existing Tectonic compiled the two-page PDF; both rendered pages were visually inspected. A subproblem notation correction was compiled and rechecked.
