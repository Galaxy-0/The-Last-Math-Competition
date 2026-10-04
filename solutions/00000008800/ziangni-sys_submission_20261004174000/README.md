# Counterexample to 00000008800

For the actual matrix A=diag(1,0), sample a uniform diagonal index J in {0,1} and output 2*A[J,J]. This reproducible randomized trace estimator is unbiased with nonzero variance 1. Averaging m independent repetitions has actual variance 1/m. Its ratio to the source's claimed scale 1/sqrt(m) tends to zero, and no positive multiple of the reciprocal-root scale is an eventual lower bound.

This separates variance from standard deviation: the latter is 1/sqrt(m) in this example. The source explicitly says variance in both languages. The benchmark quantity used is the variance across independent seeds of the arithmetic-mean output. No assertion against Bernoulli concentration is made.

Lean constructs the finite seed PMF, matrix, estimator and actual finite product probability measures. It proves marginals, iIndepFun, identical distributions, unbiasedness, actual ProbabilityTheory.variance for all m>0, the asymptotic ratio and the failure of every positive reciprocal-root lower bound.

## Reproduce

With Lean 4.19.0, run `lake update`, `lake exe cache get`, then `lake build` in `lean/`. Mathlib is pinned to c44e0c8ee63ca166450922a373c7409c5d26b00b. Public Git configuration is included; ignored local dependency junctions are not submitted.

Compile `report.tex` with a LaTeX engine supporting its standard packages. The included PDF was generated with Tectonic. See `VERIFICATION.md` for recorded checks.
