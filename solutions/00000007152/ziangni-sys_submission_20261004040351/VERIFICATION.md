# Verification evidence

Validated on 4 October 2026 with Lean 4.19.0 and Mathlib commit c44e0c8ee63ca166450922a373c7409c5d26b00b.

- Fresh project build and final revised `lake build` succeeded (1223 jobs).
- Direct final `lake env lean Main.lean` succeeded.
- The five printed axiom audits use exactly `[propext, Classical.choice, Quot.sound]`, including the three actual largest-eigenvalue proofs, absence of an actual common Basis, and the final combined counterexample.
- Largest eigenvalues are proved from nonzero eigenvector witnesses and quadratic-form bounds for every competing eigenvalue. No eigenvalue table or noncommutation datum is assumed.
- The no-common-eigenbasis theorem accepts an actual Lean Basis with arbitrary index type and shows that simultaneous eigenvectors would force equality of the composed linear maps. Evaluation on the actual vector (0,0,1) contradicts that equality.
- The exact Weyl equality is the largest-eigenvalue upper bound. Simultaneous equality in every Weyl bound is not claimed.
- No `sorry`, `admit`, `native_decide`, or extra axioms occur in the Lean source.
- Tectonic compiled the included one-page A4 PDF (30560 bytes). Poppler rendered the entire page, which was visually inspected: matrix entries, formulas, margins, and text are legible without clipping.
- The built-in LaTeX compiler was attempted and encountered its known platform-directory lookup failure; Tectonic produced the included PDF.
- Text sources use LF. Dependency caches and local junctions are ignored and excluded from the submission.
