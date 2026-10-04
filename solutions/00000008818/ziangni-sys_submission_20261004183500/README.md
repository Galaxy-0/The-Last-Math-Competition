# Counterexample to 00000008818

For the actual smooth strictly convex objective f(x)=x^4 on the real line, a genuine BFGS run with positive Hessian estimates and valid Armijo-strong Wolfe unit steps converges only linearly. Choose r in [3/4,4/5] with r^3+r^2=1. Then x_n=r^n and B_n=4x_n^2/(1-r) satisfy the full scalar Hessian BFGS update. The error ratio is exactly r, so does not tend to zero.

The unique global minimizer is attained at zero. The proof checks the actual derivative, full update, positive curvature, descending directions, Armijo constant 1/100, strong Wolfe constant 9/10, convergence and failure of superlinear convergence. Smooth means globally C-infinity here; the objective is strictly convex but its Hessian at zero vanishes. Global gradient Lipschitz continuity is not claimed. Only the source's unqualified deterministic superlinear-convergence clause is refuted, not standard results imposing nondegeneracy or the separate stochastic clause.

## Reproduce

With Lean 4.19.0, run `lake update`, `lake exe cache get`, then `lake build` in `lean/`. Mathlib is pinned to c44e0c8ee63ca166450922a373c7409c5d26b00b. Public Git configuration is included; ignored local dependency junctions are not submitted.

Compile `report.tex` with a LaTeX engine supporting its standard packages. The included PDF was generated with Tectonic. See `VERIFICATION.md` for validation details.
