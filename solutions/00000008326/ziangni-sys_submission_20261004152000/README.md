# Disproof of 00000008326

The universal algebraic-independence conjunct fails for the actual factorial Liouville series L = sum(n >= 0) 10^(-n!) and L+1. They are distinct Liouville (therefore Mahler U1) numbers, individually transcendental, and satisfy the nonzero rational polynomial Y-X-1. The report cites the standard U1 characterization and makes no assertion about the remaining conjuncts.

`lean/Main.lean` proves the full rational approximation property, its preservation by translation, transcendence, distinctness, actual multivariate polynomial evaluation, and failure of Mathlib's `AlgebraicIndependent`. The final theorem is `Counterexample.counterexample`.

Reproduce with Lean 4.19.0:

```sh
cd lean
lake exe cache get
lake build
```

Mathlib is pinned to `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The committed Lake manifest records public dependency pins. Generate the PDF using `tectonic report.tex` from this directory.
