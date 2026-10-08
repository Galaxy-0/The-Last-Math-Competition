# Verification

Use Lean4.19.0 and run `lake build` from `lean/`. Mathlib is pinned to c44e0c8ee63ca166450922a373c7409c5d26b00b; the manifest records public transitive pins. Ignored local cache junctions are not part of the submission.

The principal theorem audits use only standard logical axioms: propext, Classical.choice, Quot.sound (some use fewer). There are no proof placeholders, custom axioms, native-decision shortcuts or unsafe proof code.

The proof checks the actual CPTP identity channel at every finite ancillary dimension. The finite-ensemble symmetrization definition allows a separate finite probability distribution for each input. Both nontrivial density matrices are checked for positivity and trace1. The final contradiction proves failure at one use, which is a necessary part of the usual all-block definition, not an asserted equivalence between these notions.

The report was compiled by existing Tectonic after the built-in LaTeX compiler reported its known platform-directory failure. Every rendered PDF page was visually inspected.
