# Disproof of conjecture 00000007790

Let `Y` have the rate-one exponential distribution and set `X = Y − 1`. Its law has a measurable log-concave density, mean zero, and second moment one, so it is isotropic in dimension one. Its right tail is `P(X > u) = exp(−(u+1))` for `u ≥ −1`. Therefore its norm tail cannot satisfy `P(|X| ≥ A t) ≤ exp(−c t²)` for any positive constants `A,c`, even for all sufficiently large `t`.

This refutes the first universal assertion in the exact bilingual [conjecture](https://github.com/The-Last-Math-Competition/The-Last-Math-Competition/blob/0862407ef50dda4f7376342ca3e79368dce942d2/conjectures/00000007790.md), copied in `conjecture.md`. Both versions permit dimension one. A single fully qualifying distribution suffices; the later claims about optimality and extremizers are not used.

## What Lean proves

The law is the actual `Measure.map` of Mathlib's `expMeasure 1`. The project proves that it equals the Lebesgue measure with the explicit shifted exponential density. It establishes normalization and integrable first and second moments, and proves the full pointwise log-concavity inequality, including zero-density points and endpoint weights.

The right-tail theorem derives actual interval probabilities from Mathlib's exponential CDF. A proved event inclusion gives a lower bound for the absolute-value tail. No exact absolute-tail formula, simulation, sampled data, or assumed distribution moments are used.

The final `conjecture7790_counterexample` supplies the admissible law and defeats every pair of positive constants and every starting threshold. `conjecture7790_disproof` negates `OneDimensionalGaussianClaim`, the necessary dimension-one consequence of the original universal concentration statement. The distinction between the full statement and its necessary consequence is explicit in both the theorem documentation and report. The law's admissibility and the violation are proved unconditionally.

All declarations are in namespace `Conjecture7790`.

| File | Role |
|---|---|
| `Definitions.lean` | Actual law, explicit density, conventional log-concavity, isotropic moments |
| `Law.lean` | Equality between the pushed-forward law and the stated density |
| `LogConcavity.lean` | Full log-concavity, positive support, concavity of the logarithm |
| `Moments.lean` | Normalization, integrability, all natural exponential moments, isotropy |
| `Tail.lean` | Exact open right tail, norm-tail lower bound, violation for every constant |
| `Conjecture7790.lean` | Admissibility, explicit counterexample, final negation |
| `Check.lean` | Definition printouts, 24 theorem/instance checks and axiom audits |

The first five files above are under `lean/Conjecture7790/`; the last two are under `lean/`.

## Reproduction

Lean **4.19.0** and Mathlib **v4.19.0** are pinned. Mathlib's exact revision is `c44e0c8ee63ca166450922a373c7409c5d26b00b`, with all dependency revisions in `lean/lake-manifest.json`. From `lean/`:

```sh
lake exe cache get
lake build
lake env lean -DwarningAsError=true Conjecture7790/Definitions.lean
lake env lean -DwarningAsError=true Conjecture7790/Law.lean
lake env lean -DwarningAsError=true Conjecture7790/LogConcavity.lean
lake env lean -DwarningAsError=true Conjecture7790/Moments.lean
lake env lean -DwarningAsError=true Conjecture7790/Tail.lean
lake env lean -DwarningAsError=true Conjecture7790.lean
lake env lean -DwarningAsError=true Check.lean
```

The cache command is optional and only downloads compiled dependencies. If its executable is unavailable, the source runner is `lake env lean --run .lake/packages/mathlib/Cache/Main.lean get`. The submission itself must still be built.

`main.tex` and `main.pdf` contain the complete proof, definition correspondence, and scope explanation. `SEMANTIC_REVIEW.md` and `verification/` preserve internal review and local verification evidence. No auxiliary numerical code is needed. These checks are separate from official maintainer acceptance.
