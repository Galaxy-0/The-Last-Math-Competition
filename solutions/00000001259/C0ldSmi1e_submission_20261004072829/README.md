# Disproof of conjecture 00000001259

The actual incidence matrix of `a → ab, b → ac, c → a` has characteristic polynomial `X³ − X² − X − 1` and discriminant `−44`. If its three eigenvalues were real, counted with algebraic multiplicity, the discriminant would be a square of a real number and hence nonnegative. This contradicts the explicit three-real-eigenvalues assertion in both versions of the conjecture.

## Formal scope

The Lean project constructs the substitution as lists on `Fin 3`, defines the incidence entries using `List.count`, casts that matrix to the reals, and computes its actual `Matrix.charpoly`. It proves the discriminant obstruction using Mathlib's `Cubic` identities, permitting repeated roots. A separate theorem verifies the transpose convention has the same characteristic polynomial.

`threeRealEigenvalues` says that the actual characteristic polynomial has three real roots counted with multiplicity. Its equivalence to splitting over the real field is proved using the matrix dimension. The final theorem `conjecture1259_disproof` negates this predicate.

The exact bilingual statement is preserved in `conjecture.md`. The submission refutes its explicit necessary assertion of three real eigenvalues. It does not invent a definition of “spectral hull” or separately formalize a hull dimension, the second eigenvector, or the `0.54…` coefficient. The substitution matrix is determined by the finite images, so constructing the infinite fixed word is unnecessary for this obstruction.

## Reproduction

Lean **4.19.0** and Mathlib **v4.19.0** are pinned; Mathlib's exact revision is `c44e0c8ee63ca166450922a373c7409c5d26b00b`. From `lean/`:

```sh
lake exe cache get
lake build
lake env lean -DwarningAsError=true Conjecture1259.lean
lake env lean -DwarningAsError=true Check.lean
```

The optional cache command downloads compiled dependencies. It does not replace building the submission itself. On systems unable to run that cache executable, the source runner is `lake env lean --run .lake/packages/mathlib/Cache/Main.lean get`.

All declarations are in namespace `Conjecture1259`. `Check.lean` prints the substitution, counted matrix, cubic, and conjecture predicate, and checks ten theorem types and their axiom dependencies. No numerical auxiliary program is used or required.

`main.tex` and `main.pdf` give the complete argument and scope explanation. `SEMANTIC_REVIEW.md` and `verification/` record internal scrutiny, local validation, eligibility, and file hashes. Local verification is distinct from official maintainer acceptance.
