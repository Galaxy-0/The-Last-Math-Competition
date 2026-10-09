# Disproof of 00000008852

For every a>0, take the bounded linear operators A=aI and B+=2aI, B−=−2aI on the real Hilbert space R. The optimal strong monotonicity constant of A is a. Both perturbations have norm 2a, but A+B+=3aI is maximal monotone while A+B−=−aI is not monotone. Choosing a=ε/4 gives arbitrarily small absolute perturbation norms.

This disproves the English statement's pointwise “exactly when” criterion. It does not refute a sufficient guarantee uniform over all bounded perturbations, or a sharp worst-case threshold (a possible reading of the Chinese threshold wording). The report explains this distinction explicitly. The other clauses of the conjunction are not needed.

## Reproduction

`report.tex` and `report.pdf` contain the complete proof. `lean/Main.lean` uses genuine continuous linear maps and Mathlib's operator norm; maximal monotonicity is defined by no proper monotone extension among all relations, and proved directly.

With Lean 4.19.0, run `cd lean`, `lake exe cache get`, then `lake build`. Mathlib is pinned to `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The build prints seven principal theorem axiom audits. Run `tectonic report.tex` to reproduce the PDF. No numerical auxiliary code is required.
