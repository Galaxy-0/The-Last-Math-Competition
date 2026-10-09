# Verification

Run `lake build` inside `lean/` using Lean 4.19.0. Mathlib is pinned to c44e0c8ee63ca166450922a373c7409c5d26b00b with public transitive pins. Local cache junctions are ignored.

Lean works uniformly over real and complex scalars through RCLike. It constructs the correction as an actual continuous linear map from the inner-product functional and scalar multiplication, proves the corrected equation and exact operator norm, identifies its actual range as the residual span, and proves exact rank one for nonzero residual. A universal lower bound establishes a least element and the actual infimum over all feasible perturbation norms; the final theorem supplies a rank-one optimizer.

All 11 principal theorem audits use only propext, Classical.choice and Quot.sound. No proof placeholders, custom axioms, native-decision shortcuts or unsafe proof code occur.

Existing Tectonic compiled the report after the native compiler's platform-directory failure. Every rendered PDF page was visually inspected. The report states the absolute operator-norm, unstructured A-only convention, the nonzero approximate-vector condition, the zero-residual degeneration, and the application to arbitrary tridiagonal original matrices.
