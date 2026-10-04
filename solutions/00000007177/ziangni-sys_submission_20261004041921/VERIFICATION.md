# Verification evidence

Validated on 4 October 2026 with Lean 4.19.0 and Mathlib commit c44e0c8ee63ca166450922a373c7409c5d26b00b.

- Fresh submission project and final revised `lake build` succeeded (1103 jobs).
- Direct final `lake env lean Main.lean -DwarningAsError=true` succeeded.
- All seven printed axiom audits use exactly `[propext, Classical.choice, Quot.sound]`, including both positive-definiteness proofs, actual pencil eigenvalue, full A spectrum, quotient exclusion, and final counterexample.
- Actual matrix-vector equations define ordinary and generalized eigenvalues through nonzero eigenvectors. Positive definiteness quantifies every nonzero vector's actual quadratic form. The full A spectrum is proved in both directions; exclusions for B are derived from actual coordinates.
- Generalized eigenvalue 1 cannot be any quotient of individual eigenvalues, with arbitrary pairing and nonzero denominator. No asserted spectral tables or scalar definiteness data are used.
- The report explicitly distinguishes the valid generalized Rayleigh quotient and spectral interval bounds from an individual-spectra quotient description. The source's separate extremum clause is not addressed or needed.
- No `sorry`, `admit`, `native_decide`, or extra axioms occur in the proof.
- Tectonic compiled the included one-page A4 PDF (27195 bytes). Poppler rendered the complete final page, which was visually inspected for matrix entries, formula readability, margins, and clipping.
- The built-in LaTeX compiler was attempted and encountered its known platform-directory lookup failure; Tectonic produced the included PDF.
- Text sources use LF. Dependency caches and local junctions are ignored and excluded from the submission.
