# Conjecture 00000009761: disproved as written

The proposed bound is false for the actual complex matrix `A = [[1, 3/2], [0, 1]]`. Its characteristic polynomial is `(t-1)^2`, so both eigenvalues are 1 when counted with algebraic multiplicity. Its singular values are 2 and 1/2, certified both by the characteristic polynomial of `A* A` and by a complete unitary SVD. At `n = 2`, the conjectured right-hand side is `3/4 < 1`.

Both supplied language versions allow trace-class operators without a normality or self-adjointness restriction. Every operator in the exhibited finite dimension is trace class; the verified singular values padded by zeros have sum 5/2. The example refutes the universal inequality itself. No claim about a version restricted to normal operators, or about the validity of the classical product inequality, is made.

## Contents

- `main.tex`, `main.pdf`: complete proof, exact SVD, and formalization correspondence.
- `SOURCE.md`: exact bytes of the original bilingual statement.
- `lean/Main.lean`: actual matrix, characteristic polynomials and root multisets, unitary factors, SVD, order/sign checks, Euclidean-space adjoint bridge, summable singular sequence, and counterexample theorems.
- `lean/lean-toolchain`, `lean/lakefile.toml`, `lean/lake-manifest.json`: portable pinned Lean project.
- `verify.py`: separate matrix computations and inequality checks over exact rational numbers, using Python's standard library.
- `verification/BUILD.json` and adjacent logs: actual fresh-build and PDF evidence.
- `verification/SELF_REVIEW.md`: authoring-agent adversarial review.

## Reproduce

Install Lean through elan, then run inside `lean/`:

```text
lake build
lake env lean -DwarningAsError=true Main.lean
```

The toolchain is Lean 4.19.0. Mathlib is pinned to public Git commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`; the manifest pins all transitive dependencies. The submitted project contains public Git URLs and no local dependency paths. On a fresh machine, `lake exe cache get` may be used to obtain the official Mathlib cache before building.

From the submission directory:

```text
python verify.py
tectonic main.tex
```

## Formalization boundary

`OrderedEigenvalues` specifies the complete characteristic-polynomial root multiset and decreasing modulus order. It counts repeated eigenvalues twice, as required here. `OrderedSingularValues` requires actual complex unitary matrices whose product with an ordered nonnegative diagonal equals the submitted matrix. It is the standard finite-dimensional SVD certificate, not an unconstrained numerical list. The separate Gram characteristic polynomial provides another check of the same singular values.

The actual operator is constructed on Mathlib's complex `EuclideanSpace (Fin 2)` as a continuous linear map. Mathlib's conjugate-transpose/adjoint theorem proves that the matrix adjoint used in the proof is the Hilbert-space adjoint. The zero extension of the verified singular-value list has a Lean `HasSum` proof with sum 5/2. This is the finite-dimensional trace-class criterion used in the paper. The project does not claim a general-purpose `TraceClass` API, a formal proof of Lidskii's theorem, or the theory of compact operators in arbitrary dimension.

`conjecture_false_in_dimension_two` negates the universal inequality for those actual finite-dimensional spectral data. `full_counterexample` collects the witness, its complete spectral certificates, its summable singular sequence, and the failed bound. A universal assertion about trace-class operators must include this two-dimensional case. At `n = 2`, the positive root in the conjecture is the real square root.

## Verification and review

The exact commands, exit codes, theorem axioms, submitted-source hashes, PDF compile results, and page-review status are recorded in `verification/BUILD.json`. Validation uses a fresh directory without this submission's own build artifacts; only unmodified dependencies at the pinned official commits are reused. No proof gaps, custom axioms, opaque declarations, or native computation shortcuts are used.

The native source editor was requested and the built-in compiler was attempted. Its platform-directory failure is preserved in `verification/native-compiler.json`; the actual PDF is produced by the existing Tectonic installation and checked by page rendering.

This package receives authoring-agent self-review. The parent agent performs a separate adversarial review and current upstream source/duplicate check before publication. No GitHub write is performed by the authoring agent.
