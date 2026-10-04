# Verification

The whole Main.lean source passed Lean 4.19.0 with warningAsError=true. The five printed principal axiom audits list only propext, Classical.choice and Quot.sound. No sorry, admit, custom axiom or native_decide occurs in the source.

The project uses the actual Mathlib orthogonal reflection, projection and linear isometry equivalence APIs. The explicit predicate requires a representing linear map, surjectivity, metric isometry, and all inner products preserved. Arbitrary finite lists are evaluated as genuine successive reflection compositions. Closed subspaces of complete ambient spaces obtain their projection by a proved completeness instance.

The public configuration pins Mathlib commit c44e0c8ee63ca166450922a373c7409c5d26b00b and Lean 4.19.0; lake-manifest.json records transitive public Git revisions. A fresh local project build was run using the unchanged shared pinned dependency cache. No shared cache extension or lake clean was needed.

The built-in LaTeX compiler was attempted and returned the platform-directory error documented in the run protocol. Tectonic compiled the actual report PDF. Every final page was rendered and visually inspected for mathematical content, layout and clipping. All text files use LF bytes and git diff --check passed before commit.
