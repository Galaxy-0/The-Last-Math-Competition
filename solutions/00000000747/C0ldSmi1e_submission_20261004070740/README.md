# Disproof of conjecture 00000000747

For every prime `p ≥ 5`, the actual p-adic integer `-1 ∈ Z_p` is distinct from `0` and `1` and satisfies `(-1)^p = -1`. Every iterate of the power map fixes it. In particular, `p = 5` refutes the assertion that only `0` and `1` can be fixed points or points fixed by positive iterates.

The proof uses Mathlib's actual `PadicInt p` and `Function.iterate`. Its final theorem negates the universal conjecture predicate. No finite residue calculation replaces the p-adic domain, and no Hensel lifting is needed for this explicit witness.

## Previous submission and scope

[PR35](https://github.com/The-Last-Math-Competition/The-Last-Math-Competition/pull/35) was initially merged, then [removed in the maintainer re-audit](https://github.com/The-Last-Math-Competition/The-Last-Math-Competition/commit/541cf4fbc7aef3e17085577f6403c11c09f31fe1). The conjecture is currently unsolved. The earlier Lean file established only finite congruences, without the connection to a p-adic root. Its report also incorrectly claimed `p^n` p-adic fixed points for the `n`-th iterate; the simple-root Hensel argument actually gives `p` for positive `n`. See `PRIOR_SUBMISSION.md` and the report for the complete error account and immutable source links.

The exact bilingual conjecture is preserved in `conjecture.md`. “Superattracting orbits” appears only as a parenthetical, without a derivative-zero hypothesis. The submitted claims concern ordinary fixed points and positive iterates. We do not assert that `-1` is superattracting or claim a formal classification of all periodic roots.

## Reproduction

The project pins Lean **4.19.0** and Mathlib **v4.19.0**, commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`. From `lean/`:

```sh
lake exe cache get
lake build
lake env lean -DwarningAsError=true Conjecture747.lean
lake env lean -DwarningAsError=true Check.lean
```

The cache command is optional; it downloads compiled dependencies instead of rebuilding them locally. The submission module itself must still be built.

- `conjecture747_disproof` negates `iterativeFixedPointClaim`.
- `not_directFixedPointClaim` negates the ordinary fixed-point claim.
- `counterexample_every_prime` gives the actual p-adic witness for every prime at least five and every natural iterate.
- `concrete_counterexample` specializes to `PadicInt 5`.

All declarations above are in namespace `Conjecture747`. `Check.lean` prints the domain definition, conjecture predicates, theorem types, and eight axiom audits. No numerical auxiliary program is used or required.

`main.tex` and `main.pdf` contain the complete argument and historical correction. `SEMANTIC_REVIEW.md` and `verification/` record internal review, local checks, exact dependency pins, and artifact hashes. Local verification is separate from official maintainer acceptance.
