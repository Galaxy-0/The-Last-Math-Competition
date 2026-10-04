# Disproof of conjecture 00000000360

The optimal uniform constant for the stated homogeneous diagonal problem is **zero**, in every dimension at least two. For every diagonal coefficient matrix, the nonzero integer vector `(1,0,...,0)` makes the product of the linear forms zero. This is also the global minimum of the absolute product.

At dimension ten, `K = 10!/10^10` is positive, and the strictly smaller positive constant `K/2` works uniformly. Hence the claim that `K` cannot be improved is false, whether admissible constants are nonnegative or strictly positive. The Lean result covers all real diagonal coefficients and separately covers the nonsingular class.

## Exact scope

The exact bilingual source is preserved in `conjecture.md`. Here “diagonal” means `L_i(x) = a_i*x_i` in the given integer coordinates. Both source versions require a nonzero integer vector, not a vector with all coordinates nonzero; neither version introduces affine shifts or excludes zero products.

The disproof concerns the sharpness conjunct. It does not claim the separate convex-body clause is false. The report distinguishes the written homogeneous formula from the classical Minkowski formulation with arbitrary shifts. It also acknowledges the administrative scoring discussion in PR #5; no earlier solution submission was identified.

## Files and reproduction

- `main.tex` and `main.pdf`: complete argument, interpretation, and formalization description.
- `lean/Conjecture360.lean`: definitions, uniform classification, explicit minimizer, and final disproof.
- `lean/Check.lean`: printed definitions, theorem types, and axiom audit.
- `lean/lean-toolchain`, `lakefile.toml`, `lake-manifest.json`: pinned reproducible project.
- `SEMANTIC_REVIEW.md` and `verification/`: internal scrutiny, validation records, and artifact hashes.

The project uses Lean **4.19.0** and Mathlib **v4.19.0**, with Mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b` pinned in the manifest. From `lean/`:

```sh
lake exe cache get
lake build
lake env lean -DwarningAsError=true Conjecture360.lean
lake env lean -DwarningAsError=true Check.lean
```

The cache command is optional: it downloads compiled dependencies instead of rebuilding them locally. All submission proof sources must still be built. The final theorem is `Conjecture360.conjecture360_disproof : ¬ Conjecture360.optimalityClaim`.

There is no auxiliary numerical computation to run. The proof uses actual Mathlib matrix multiplication and determinants, actual integer vectors, arbitrary real coefficients, and full quantifiers. It contains no admitted proofs, custom axioms, or `native_decide`. Local verification is separate from official maintainer acceptance.
