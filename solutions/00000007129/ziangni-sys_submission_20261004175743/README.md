# Counterexample to 00000007129

For the nondegenerate planar LP maximizing 2x+y over x,y>=0, x<=5, 4x+y<=25, the complete vertex-edge graph is a four-cycle of diameter two. Ordinary Dantzig simplex from the origin makes three unique pivots, through (5,0), (5,5), and (0,25). Thus its worst-case pivot count is at least three and cannot equal the graph diameter.

The report explicitly distinguishes Dantzig's ordinary largest-positive-reduced-cost rule from a pivot rule chosen to follow shortest paths. Only the asserted equality with worst-case simplex steps is refuted; the separate monomial diameter-bound clause is not addressed.

The Lean project verifies the actual real halfspace set and its full Mathlib extreme-point set, supporting-functional edge criterion, actual SimpleGraph diameter, all four standard-form dictionaries for every equality-feasible vector, basis partitions and nondegeneracy, reduced costs, unique entering/leaving variables, exact feasible-ray intervals, pivot transitions, and the unique terminal optimum. The final certificate combines all three Dantzig pivots with a graph walk longer than the diameter.

## Reproduce

With Lean 4.19.0, run `lake update`, `lake exe cache get`, and `lake build` in `lean/`. Mathlib is pinned to c44e0c8ee63ca166450922a373c7409c5d26b00b. Public Git dependency configuration is included; ignored local dependency junctions are not submitted.

Compile `report.tex` with a LaTeX engine supporting the listed standard packages. The included two-page PDF was produced with Tectonic. Validation details are in `VERIFICATION.md`.
