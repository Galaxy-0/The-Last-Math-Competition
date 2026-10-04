# Disproof of 00000008341

The source's explicit formula `2-(w+1)` predicts dimension -1 at w=2. The classical Jarnik set of irrational points in [0,1] with error less than q^(-3) at arbitrarily large denominators is nonempty, and its actual Hausdorff dimension lies between zero and one.

Lean defines the complete approximation set, shows the actual factorial Liouville series belongs to it, and uses Mathlib's actual Hausdorff dimension. Finiteness is proved before the real-valued dimension is compared to -1. The final theorem is `Counterexample.counterexample`. This refutes the dimension conjunct; the report does not claim to resolve the remaining clauses or formalize the exact classical Jarnik–Besicovitch dimension formula.

Reproduce with Lean 4.19.0:

```sh
cd lean
lake exe cache get
lake build
```

Mathlib is pinned to `c44e0c8ee63ca166450922a373c7409c5d26b00b`; the public dependency manifest is included. Compile the report from this directory with `tectonic report.tex`.
