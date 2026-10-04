# Conjecture 00000008574: claimed Schatten constant fails atp=1/2

For actual1×1 complex identity matrices A=B=I, the actual singular values are1,1, and2 for A+B. The genuine finite-dimensional Schatten formula gives values1,1,2 atp=1/2. The claimed coefficient2^(1−1/p) is1/2, so the triangle estimate would be2≤1. The general-p clause is false; other clauses are not addressed.

Files: report.tex/report.pdf, reproducible lean/ project, verification/ evidence. No numerical auxiliary code is needed.

With Lean4.19.0 run `cd lean`, `lake build`, then `lake env lean -DwarningAsError=true Main.lean`. The project pins Mathlib v4.19.0; ignored local cache junctions are not required for reproduction. Compile with `tectonic report.tex`.

Main.lean uses actual complex matrices, conjugate transpose, Gram multiplication, actual nonzero-vector eigenvalue conditions, square roots, finite sums and Real.rpow. The full1×1 eigenvalue characterization proves the sole Gram eigenvalue, and the singular-value array is its nonnegative square root. The exact standard Schatten specialization and coefficient are computed, and the universal triangle-bound predicate is negated. No arbitrary scalar norm or singular-value data are asserted.
