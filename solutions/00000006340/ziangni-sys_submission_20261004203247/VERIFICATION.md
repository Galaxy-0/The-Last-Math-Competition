# Validation

Final full lake build succeeds (1578 targets), without warnings. All twelve printed axiom audits use only standard propext, Classical.choice and Quot.sound. No admissions or custom axioms occur. Actual real matrices, invertible rank preservation for every perturbation, entry-change counting, all rank-dependent cost sets, attained minima, complete complex eigenvalue characterizations and both notions of orthogonality are proved.

Existing Tectonic compiled the two-page PDF (36695 bytes) without box warnings. Both rendered pages were visually inspected and are clean. The built-in compiler was attempted and encountered the known platform-directory failure. Public Lean 4.19.0 and Mathlib c44e0c8ee63ca166450922a373c7409c5d26b00b pins remain unchanged; no shared cache extension was needed. Text is UTF-8 LF and the scoped diff check passes.

The full rigidity equality is for standard entry-change matrix rigidity. Distinct spectra implement the source's explicit same-rank-changes/different-eigenvalues separation.
