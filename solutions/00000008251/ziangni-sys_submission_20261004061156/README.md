# Counterexample to conjecture 00000008251

Two Arrow securities on two states have payoff matrix I₂ and initial prices (1/2,1/2). Their full martingale-probability set is the singleton uniform measure, including under the equivalent-measure convention. It has one actual extreme point, whereas the conjectured formula gives |Omega| minus asset rank = 2-2=0.

The market is complete and arbitrage-free. The two securities replicate the constant numeraire, so the rank calculation does not depend on counting a separate bond.

- `report.tex`, `report.pdf`: complete proof and scope.
- `lean/Main.lean`: actual payoff matrix/rank, portfolio replication and no-arbitrage, genuine probability measure and Bochner expectation equations, full measure uniqueness, absolute continuity, and Mathlib extreme-point count.
- `VERIFICATION.md`: validation and eligibility.

Use Lean 4.19.0. From `lean/`, run `lake update`, `lake exe cache get`, `lake build`, and `lake env lean Main.lean -DwarningAsError=true`. Mathlib is pinned to `c44e0c8ee63ca166450922a373c7409c5d26b00b`. Compile the report with `tectonic report.tex`.
