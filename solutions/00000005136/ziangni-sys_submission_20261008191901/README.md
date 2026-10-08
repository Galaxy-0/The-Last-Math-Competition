# Proof of 00000005136

For fixed x != 0 and residual r = b - A x, the actual rank-at-most-one operator Delta(v) = <x,v> r / ||x||² satisfies (A + Delta)x = b and has exact induced operator norm ||r||/||x||. Every feasible perturbation has norm at least this ratio. The feasible-norm set has this value as its least element and genuine infimum. The correction's range is span{r}, so its rank is exactly one for nonzero residual.

The theorem is general over real or complex inner-product domains and normed target spaces. It covers every tridiagonal original matrix under the stated absolute, unstructured, A-only operator-norm convention. Zero residual needs the zero correction; structured, relative, or joint data perturbations are separate models.

Run `lake build` in `lean/` with Lean 4.19.0 and the pinned public dependencies. Full proof and convention details are in `report.pdf` and `report.tex`.
