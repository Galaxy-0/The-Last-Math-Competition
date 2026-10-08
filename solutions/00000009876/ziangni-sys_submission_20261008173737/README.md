# Disproof of 00000009876

Take iid edge weights with law δ₁ on the nearest-neighbor square lattice Z². All weights are strictly positive, have finite second moments and every exponential moment. The actual infimum of all lattice-walk costs from (n,0) to (0,0) equals n, so its variance is zero. This contradicts any positive one-half growth law, even an eventual positive lower bound c sqrt(n).

The source does not assume a nonconstant edge law. This submission disproves the general finite-variance and finite-exponential-moment assertions as written; it makes no assertion about a restricted nondegenerate class or the separate heavy-tail clause.

## Files and reproduction

- `report.tex`, `report.pdf`: complete mathematical proof and scope discussion.
- `lean/Main.lean`: actual graph, edge random variables, all-walk cost infimum, exact passage time and measure-theoretic variance.
- `lean/lakefile.lean`, `lean/lake-manifest.json`, `lean/lean-toolchain`: pinned public dependencies.

With Lean 4.19.0 available, run `cd lean`, `lake exe cache get`, then `lake build`. The Mathlib revision is `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The build prints the axioms of all eight principal theorems. Compile the report with `tectonic report.tex` or another standard LaTeX installation.

No auxiliary numerical calculation is required.
