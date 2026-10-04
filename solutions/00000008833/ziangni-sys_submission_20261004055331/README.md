# Counterexample to conjecture 00000008833

The actual Chambolle–Pock iteration for f(x)=g(x)=x²/2 and nonzero coupling Kx=x/4 converges from every initial state with tau=sigma=2 and theta=1. The step-size product is four, contradicting the source's universal requirement that it be at most one.

The full three-coordinate update contracts the maximum absolute coordinate by a factor at most one half. The construction agrees with the usual operator-dependent sufficient condition tau*sigma*norm(K)²<1; the source imposes no normalization of K. Only the universal product-bound conjunct is refuted.

- `report.tex`, `report.pdf`: complete argument, scope, and correspondence.
- `lean/Main.lean`: actual continuous convex objectives, bounded nonzero coupling, adjoint identity, genuine Fenchel supremum, unique global proximal minimizers, saddle inequalities, actual CP update and all-state convergence.
- `VERIFICATION.md`: validation and eligibility evidence.

From `lean/`, use Lean 4.19.0 and run `lake update`, `lake exe cache get`, `lake build`, and `lake env lean Main.lean -DwarningAsError=true`. Mathlib is pinned to `c44e0c8ee63ca166450922a373c7409c5d26b00b`. Compile the PDF with `tectonic report.tex`.
