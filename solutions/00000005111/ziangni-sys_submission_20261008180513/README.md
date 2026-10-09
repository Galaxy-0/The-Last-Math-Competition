# Disproof of 00000005111

For A_t=[[0,t],[0,0]] and unit b=(0,1), the spectrum is always {0}, the ambient dimension is2, and the first Krylov space is exactly span{b}. At time1, the genuine matrix exponential sends b to (t,1). Every vector in the first Krylov space has Euclidean error at least |t|; one-step Arnoldi attains equality. Taking t=|C|+1 defeats any finite proposed spectral-only bound C.

The source states no normality or nonnormality-control hypothesis. This refutes an absolute error bound based only on the spectral interval and dimensions as written; it does not refute bounds depending on numerical range, matrix norm or conditioning, or a theorem restricted to normal matrices.

## Reproduction

`report.tex` and `report.pdf` give the complete proof. `lean/Main.lean` uses actual complex matrices, Mathlib's spectrum and canonical matrix exponential, an actual complex Krylov submodule, and the Euclidean norm written in coordinates. The exponential is evaluated from its defining series, not assumed.

With Lean4.19.0 run `cd lean`, `lake exe cache get`, then `lake build`. Mathlib is pinned to `c44e0c8ee63ca166450922a373c7409c5d26b00b`. Eleven principal theorem audits are printed. Recompile the PDF with `tectonic report.tex`. No auxiliary numerical code is required.
