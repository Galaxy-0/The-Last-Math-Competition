# Verification

Run `lake build` inside `lean/` using Lean 4.19.0. Mathlib is pinned to c44e0c8ee63ca166450922a373c7409c5d26b00b, with public transitive pins in the manifest. Local cache junctions are ignored.

The formalization uses actual real partial derivatives, a genuine multivariable polynomial, Lebesgue energy on the Euclidean disk, and the boundary integral in circle coordinates with verified derivative and tangent norm. The actual quotient is positive-denominator and identically 1 for r > 0; its derivative is proved zero by local equality, not stipulated.

The main theorem combines harmonicity, positive boundary mass, constant frequency, zero derivative and nonradiality. Principal theorem audits use only propext, Classical.choice and Quot.sound. No proof placeholders, custom axioms, native-decision shortcuts or unsafe proof code occur.

The report was compiled using existing Tectonic after the built-in compiler's known platform-directory failure, then every rendered page was visually inspected. Its scope targets the explicit saturation-only-radial conjunct, without relying on the ambiguous uniqueness clause.
