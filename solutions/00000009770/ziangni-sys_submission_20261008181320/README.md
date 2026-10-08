# Counterexample to 00000009770

The nonzero positive projections P=diag(1,0) and Q=diag(0,1) satisfy trace-norm triangle equality, but their polar support spaces are different and intersect only at zero. In the diagonal two-point measure model the positive polar measures are actual Dirac masses at different points. This refutes the literal same-support necessity, not a criterion based on a common compatible polar factor, and makes no claim against the separate exposed-face theory.

- `report.pdf` and `report.tex`: complete mathematical explanation and scope.
- `lean/Main.lean`: canonical positive-square-root trace norm, support ranges, polar factorizations, atomic measure bridge, and final counterexample.
- `VERIFICATION.md`: reproduction and validation.

Use Lean 4.19.0 and run `lake build` from `lean/`. The public Mathlib dependency is pinned to c44e0c8ee63ca166450922a373c7409c5d26b00b.
