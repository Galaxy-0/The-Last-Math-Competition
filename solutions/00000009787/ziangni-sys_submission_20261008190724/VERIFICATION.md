# Verification

Run `lake build` inside `lean/` using Lean 4.19.0. Mathlib is pinned to c44e0c8ee63ca166450922a373c7409c5d26b00b with public transitive pins. Local cache junctions are ignored.

Lean computes the genuine perturbation Gram matrix, canonical positive square root and eigenbasis/spectrum of that modulus. It proves compactness of the actual matrix action using a compact ball image, then computes full complex spectra by determinant factorization. Positive-radius neighborhoods verify isolation. The actual infimum distance to the original spectrum equals t, and the final theorem excludes every finite uniform bound for the fixed perturbation.

All 12 printed theorem audits use only propext, Classical.choice and Quot.sound. No proof placeholders, custom axioms, native-decision shortcuts or unsafe proof code occur.

The native compiler failed on its platform-directory lookup; existing Tectonic compiled the report. All rendered PDF pages were visually inspected. The scope distinguishes perturbation-only control from estimates with normality or original-operator conditioning assumptions.
