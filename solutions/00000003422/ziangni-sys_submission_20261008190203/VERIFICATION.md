# Verification

Run `lake build` inside `lean/` using Lean 4.19.0. Mathlib is pinned to c44e0c8ee63ca166450922a373c7409c5d26b00b; all transitive dependencies have public pins. Local cache junctions are ignored.

The formalization verifies the real chain's positivity, stochastic row sums, laziness, stationary probability and detailed balance, then complexifies the matrix. The fundamental matrix is defined using Mathlib's canonical nonsingular inverse and evaluated by a proved inverse identity. Determinant factorizations give the complete complex spectra. The proof excludes arithmetic and literal set complements, computes the deviation spectrum, and verifies the reciprocal nonstationary image and row sums.

All 15 principal theorem audits use only propext, Classical.choice and Quot.sound. No proof placeholders, custom axioms, native-decision shortcuts or unsafe proof code occur.

Existing Tectonic compiled the report after the native compiler's platform-directory failure. Every rendered page was visually checked. The report explicitly identifies the complement interpretations and does not claim to disprove the correct reciprocal-gap formula.
