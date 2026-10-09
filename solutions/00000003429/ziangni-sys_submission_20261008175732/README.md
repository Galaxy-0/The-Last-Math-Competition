# Disproof of 00000003429

The strictly positive, lazy, reversible transition matrix

```
5/8  1/8  1/4
1/8  5/8  1/4
1/4  1/4  1/2
```

has uniform stationary law and centered mixing spectral radius 1/2. The nonzero centered observable (1,1,−2) has stationary variance 2 and normalized autocorrelation (1/4)^n. Every consecutive-lag ratio and its root-rate limit equal 1/4, not 1/2.

The report distinguishes the false blanket equality for individual observables from an unrefuted worst-case upper bound or supremum over observables.

## Reproduction

The complete argument is in `report.tex` and `report.pdf`. `lean/Main.lean` defines the genuine transition matrix, stationary finite-sum covariance and matrix powers. Explicit bijective coordinates on the whole centered space intertwine its restriction with diag(1/2,1/4); no spectral data are assumed.

With Lean 4.19.0, run `cd lean`, `lake exe cache get`, then `lake build`. Mathlib is pinned to `c44e0c8ee63ca166450922a373c7409c5d26b00b`. Nineteen principal theorem audits are printed. Compile the PDF with `tectonic report.tex`. No numerical auxiliary code is needed.
