# Verification

Fresh project lake build and direct whole-source Lean with warningAsError=true passed. Principal printed axiom audits list only propext, Classical.choice and Quot.sound. No sorry, admit, native_decide or additional axioms occur in Main.lean.

Actual EuclideanSpace real Fin2 is used, with an actual norm-squared distance formula. The sets are proved closed and convex. Both explicit projections are proved nearest for every input and every candidate in the respective sets. Actual cycle recurrence covers every iterate, and actual topological strong convergence implies the full standard continuous-linear-functional weak convergence criterion. Actual coordinate CLMs force uniqueness of any weak limit. An actual feasible nearer point proves the final negation of nearest-point weak convergence. The full individual-step orbit, parity-based recurrence, convergence and same negation are also proved.

Lean4.19.0 and Mathlib c44e0c8ee63ca166450922a373c7409c5d26b00b are pinned by public configuration and manifest. No shared cache extension or lake clean was performed.

Built-in LaTeX source editor/compiler was attempted and returned the known platform-directory error. Tectonic compiled the final PDF; all pages were rendered and visually inspected for complete content and layout. All text files use LF bytes and git diff --check passed. Local caches/build products are ignored and excluded from the commit.
