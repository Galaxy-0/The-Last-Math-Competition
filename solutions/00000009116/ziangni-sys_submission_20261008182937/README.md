# Counterexample to 00000009116

The radial Gaussian exp(-(x²+y²)) is a pure spherical-harmonic mode of degree 0, which is even. Its actual planar hyperplane Radon transform is sqrt(pi) exp(-s²), independent of the normal angle and strictly positive. Thus the asserted even-degree annihilation fails.

The report explicitly distinguishes angular degree from signed-offset parity and the hyperplane Radon transform from the Funk transform. It identifies the literal vanishing assertion being refuted without inventing a definition for the source's otherwise unspecified 'support spectrum'.

The complete proof is in `report.pdf` and `report.tex`. The Lean project checks genuine line coordinates, arclength normalization, Lebesgue integrals, Gaussian integrability, the actual constant harmonic polynomial and its angular factor. Run `lake build` in `lean/` using Lean 4.19.0 and the pinned Mathlib dependencies.
