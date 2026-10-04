# Disproof of conjecture 00000008858

Alternating genuine metric projections between intersecting closed convex halfspaces need not converge to the nearest intersection point. In the actual Euclidean plane, A={y≥0}, B={x≤y}, and start=(2,−1) produce (2,0), then (1,1), which both projections fix. The feasible point (1/2,1/2) is strictly closer to the start: squared distances9/2<5.

The Lean project proves closedness/convexity, projection minimization for every input and every candidate, all cycle iterates and their actual strong and weak limit, uniqueness of every weak limit under the standard all-continuous-linear-functionals criterion, and absence of any nearest weak limit. It also verifies the full individually indexed projection sequence, parity-based actual recurrence, strong limit and identical nearest-limit obstruction.

This refutes the first universal nearest-point clause, without relying on an empty intersection or nonconvergence. The later rate and regularity clauses are not separately analyzed.

See report.tex and report.pdf. From lean/, run:

```text
lake build
lake env lean -DwarningAsError=true Main.lean
```

Lean4.19.0 and Mathlib c44e0c8ee63ca166450922a373c7409c5d26b00b are pinned publicly. Ignored local dependency junctions used for validation are not part of the submission.
