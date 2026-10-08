# Counterexample to 00000005714

The harmonic polynomial u(x,y) = x has actual disk Dirichlet energy pi r² and boundary squared mass pi r³, hence Almgren frequency N(r) = 1 and derivative 0 for every r > 0. It is not radial: equal-radius points on the two coordinate axes have different values. This disproves the stated saturation-only-spherical-symmetry conjunct within polynomial germs.

The complete argument is in `report.pdf` and `report.tex`. Lean verifies genuine derivatives, the Lebesgue disk integral, the circle derivative and arclength normalization, the boundary integral, quotient, frequency derivative and nonradiality. No interpretation of the separate uniqueness assertion is needed.

Run `lake build` in `lean/` with Lean 4.19.0 and the pinned public Mathlib dependencies.
