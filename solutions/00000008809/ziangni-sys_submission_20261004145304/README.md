# Disproof of conjecture 00000008809

The actual feasible two-block problem min −x subject to x−z=0 has closed proper convex objectives f(x)=−x and g(z)=0. With penalty 1 and zero initial state, exact ADMM has unique global minimizers in both subproblems but actual iterates x_k=z_k=k and multiplier 0. The residual is zero while the primal trajectory does not converge weakly. The objective has no minimizer; neither original language imposes attainment or a saddle-point hypothesis. This identifies that omitted condition and does not refute standard ADMM theorems with solution existence assumptions.

The full two-page proof is in report.tex/report.pdf. lean/Main.lean uses actual real Hilbert CLMs, real/extended-real properness, closed epigraphs and convexity, the true augmented Lagrangian, globally unique subproblem minima, full ADMM iterates and weak convergence quantified over continuous linear functionals. Verification records the original source and the single successful final full build.

From lean/ using Lean 4.19.0:

```text
lake update
lake exe cache get
lake build
```

Mathlib is publicly pinned to c44e0c8ee63ca166450922a373c7409c5d26b00b. Ignored local junctions are only cache convenience. The whole source build prints seven axiom audits; only standard logical axioms are used. No admitted facts, custom axioms or native decision procedures.

The saved LaTeX editor/compiler was attempted, with its existing platform-directory failure. Tectonic compiled the final PDF, and both pages were rendered and visually inspected. Round 2 protocol requires no routine duplicate source check or independent review.
