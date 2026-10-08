# Verification

Run `lake build` inside `lean/` using Lean 4.19.0. Mathlib is pinned to c44e0c8ee63ca166450922a373c7409c5d26b00b, with public transitive pins in the manifest. Local cache junctions are ignored.

Lean proves actual cube compactness, convexity, symmetry and origin interior, followed by the universal-pairing polar identity using a sign-vector witness. It computes product Lebesgue volumes using the box formula and the p = 1 instance of Mathlib's lp-ball volume formula, including the Gamma-to-factorial evaluation. It proves the strict dimension-12 bound violation and the dimension-3 nonattainment statement.

All 12 printed theorem audits use only propext, Classical.choice and Quot.sound. No proof placeholders, custom axioms, native-decision shortcuts or unsafe proof code occur.

The report was compiled using existing Tectonic after the built-in compiler's platform-directory failure. Every rendered page was visually inspected. The explicit normalization and dimension discussion distinguishes the source claim from the standard Mahler conjecture.
