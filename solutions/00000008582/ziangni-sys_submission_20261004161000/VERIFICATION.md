# Verification

- Lean 4.19.0, Mathlib c44e0c8ee63ca166450922a373c7409c5d26b00b.
- Final full `lake build` succeeded: 2083 targets, no warnings. Earlier development-build API errors were corrected before this final successful build.
- Eight printed theorem axiom audits contain only `propext`, `Classical.choice`, and `Quot.sound`.
- No sorry, admit, native_decide, unsafe declarations, or custom axioms.
- Actual Mathlib Hilbert sum and continuous linear maps, norm-summable operator series, compactness via closedness under limits, independent eigenvector pairs, infinitely many distinct nonzero eigenvalues, and failure of the selfadjoint inner identity are all checked.
- `MultipleEigenvalue` requires two linearly independent eigenvectors; this is stronger than the failure of algebraic simplicity needed to refute the finite-exception clause. Generic simplicity and the separate completeness claim are not asserted false.
- Built-in LaTeX compilation encountered the known platform-directory failure. Existing Tectonic compiled the final report once. Both PDF pages were rendered and visually inspected; no clipping or illegibility found. PDF size: 31807 bytes.
