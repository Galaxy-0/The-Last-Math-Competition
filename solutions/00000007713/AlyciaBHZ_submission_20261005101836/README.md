# TLMC 00000007713: corona growth equation refuted

The conjecture's two exact quantitative clauses are inconsistent. For the hyperbolic pair `{4,6}`, the equation forces `lambda + 1/lambda = 6`, so lambda is one of the quadratic irrationals `3 +/- 2*sqrt(2)`. The product `(p-2)(q-2) = 8` is absent from `{4,5,6,10}`, contradicting the stated necessary condition.

The Lean project also proves that for every integer `N >= 3`, every real solution of `x + 1/x = N` is quadratic irrational: `N^2-4` lies strictly between consecutive integer squares. This yields a contradiction for every cutoff `K`, with `p=q=max(K,6)`. Thus a restriction to sufficiently large values of both parameters does not rescue the exact clauses. No positivity or nonzero hypothesis is required: the equation excludes zero.

Contents:

- `lean4/CoronaGrowth.lean`: definitions, general arithmetic lemma, global refutation, refutation on every simultaneous tail, and axiom audits.
- `lean4/lean-toolchain`, `lakefile.toml`, `lake-manifest.json`: standalone project pinned to Lean/Mathlib `v4.33.0`.
- `report.tex` and `report.pdf`: complete mathematical proof, verbatim conjecture, interpretation discussion, formal correspondence, and verification details.
- `verification.txt`: actual successful guarded Lean compile output and optional Python check output.
- `verify.py`: exact independent finite sanity checks using only the Python standard library.

Build in a fresh environment:

```sh
cd lean4
lake exe cache get && lake build
```

Optional checks and report reproduction, from the package root:

```sh
python3 verify.py
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
```

The delivered source compiled successfully with Lean and Mathlib v4.33.0. The theorem audits use only `propext`, `Classical.choice`, and `Quot.sound`. The finite Python checks do not establish or replace the universal Lean proofs.

The equality is formalized exactly as written and "only when" as a necessary implication. Both the global family and arbitrary simultaneous-tail readings are covered. An unstated approximate equation would be a different conjecture. The true corona growth rate and the unspecified quadratic form in `2cosh` are not needed to refute the inconsistent necessary clauses.

Submitted by AlyciaBHZ on behalf of the Omega Institute (trureturing project, https://github.com/the-omega-institute/trureturing).

All proof code is newly written. No trureturing code is vendored.
