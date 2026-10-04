# Counterexample to 00000008841

On the real Hilbert space, take T(x) = -x and its actual Picard orbit from 1. Every iterate is an isometry, so asymptotic nonexpansiveness holds with coefficients k_n = 1 converging to 1. The map fixes 0 and preserves the nonempty closed bounded convex interval [-1,1]. Nevertheless its even and odd iterates are 1 and -1, so the continuous linear identity functional rules out any weak limit.

The source explicitly concerns iteration and states universal weak convergence. No averaging or asymptotic regularity hypothesis is present. Disproving this assertion disproves the source's conjunction; no interpretation of the further demiclosedness clause is needed.

## Files and reproduction

- `report.tex` and `report.pdf`: complete mathematical disproof and formal correspondence.
- `lean/Main.lean`: actual real map, function iterates, asymptotic coefficients, invariant interval and geometry, weak convergence quantified over all continuous linear functionals, and nonconvergence proof.
- `verification.txt`: checks and axiom audit.

The Lean project pins Lean 4.19.0 and Mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`. From `lean/`, run:

```text
lake exe cache get
lake build
lake env lean Main.lean
```

The final theorem is `AsymptoticIteration8841.conjecture_00000008841`; the interval geometry is `AsymptoticIteration8841.interval_geometry`. Both have only standard logical axioms. There are no numerical or auxiliary computational dependencies. Compile the report with `tectonic report.tex`.
