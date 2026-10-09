# Disproof of 00000007157

The nonnormal complex matrix J=[[0,1],[0,0]] has spectrum and topological spectral frontier {0}. Its genuine numerical radius satisfies 12/25 ≤ w(J) ≤ 1/2, so it is positive. Every semicircle of that radius has distinct endpoints, for any center and orientation, and cannot equal the singleton frontier.

This addresses the literal assertion that the spectral boundary is a semicircle. It does not refute a possible enclosure inequality, which would be a different statement. The report states this scope explicitly.

## Reproduction

`report.tex` and `report.pdf` provide the full proof. `lean/Main.lean` uses an actual complex matrix, Mathlib spectrum and topological frontier, conjugate transpose, and the supremum of quadratic-form moduli over Euclidean unit vectors. The formal conclusion quantifies over all translated and rotated semicircles.

With Lean 4.19.0, run `cd lean`, `lake exe cache get`, then `lake build`. Mathlib is pinned to `c44e0c8ee63ca166450922a373c7409c5d26b00b`. Six principal theorem audits are printed. Recompile the PDF with `tectonic report.tex`. No numerical auxiliary code is needed.
