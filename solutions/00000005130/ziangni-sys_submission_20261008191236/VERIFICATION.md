# Verification

Run `lake build` inside `lean/` using Lean 4.19.0. Mathlib is pinned to c44e0c8ee63ca166450922a373c7409c5d26b00b with public transitive pins. Local cache junctions are ignored.

Lean verifies positive definiteness, canonical matrix inverses, complete real spectra of preconditioners and preconditioned systems, and the common iteration spectrum. Error sequences are defined by the actual matrix recurrence, and the resulting iterates satisfy preconditioned Richardson's update. Exact Euclidean error norms and first-iterate separation are proved. A proper orthogonal quarter-turn conjugates the preconditioners and the entire trajectories with a rotated initial direction.

All 16 principal theorem audits use only propext, Classical.choice and Quot.sound. No proof placeholders, custom axioms, native-decision shortcuts or unsafe proof code occur.

The report was compiled using existing Tectonic after the native compiler's platform-directory failure. Every rendered PDF page was visually inspected. The proof supplies the full existential example stated by both source versions.
