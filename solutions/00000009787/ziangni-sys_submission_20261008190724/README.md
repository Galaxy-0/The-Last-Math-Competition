# Counterexample to 00000009787

On complex dimension two, A_t = [[0,t²],[0,0]] has spectrum {0}. The fixed compact perturbation E = [[0,0],[1,0]] has canonical positive modulus diag(1,0), hence singular values (1,0), while A_t + E has spectrum {t,-t}. Its displacement from the original spectrum is t, which is unbounded for t > 0.

This rules out every finite bound depending only on the perturbation singular-value sequence. The original operator norm is unconstrained and the matrices are nonnormal; the report explicitly preserves normal and condition-dependent perturbation estimates.

Run `lake build` in `lean/` with Lean 4.19.0 and the pinned public dependencies. See `report.pdf` and `report.tex` for the full proof and exact scope.
