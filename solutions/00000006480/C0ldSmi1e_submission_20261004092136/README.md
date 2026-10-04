# Proof of conjecture 00000006480

Let `A,B,C` be the three coordinate signs on the uniform eight-outcome sign cube. The explicit processes

```text
X = (A, B, C)
Y = (A, B, A B)
```

have mean zero and the same covariance matrix `I₃`. Their joint laws differ, and their maximum laws are

```text
law(max X) = (1/8) δ₋₁ + (7/8) δ₁
law(max Y) = δ₁.
```

Both processes are non-Gaussian: their first coordinate has an atom of mass `1/2`, impossible for any real Gaussian law, including a variance-zero point mass.

## Statement and scope

The exact [English and Chinese conjecture](https://github.com/The-Last-Math-Competition/The-Last-Math-Competition/blob/0862407ef50dda4f7376342ca3e79368dce942d2/conjectures/00000006480.md) is copied in `conjecture.md`. Both versions ask for an explicit non-Gaussian pair with equal covariance and different extremal and joint distributions. Neither requires an infinite time index, stationarity, continuity, nor a limiting normalization. Here the extremal distribution is the law of the maximum over the three process indices. The final theorem supplies concrete finite-process witnesses for the existential claim.

Finite indexed families are processes under the standard convention; see Rasmussen and Williams, [*Gaussian Processes for Machine Learning*, §2.2](https://gaussianprocess.org/gpml/chapters/RW2.pdf). The Gaussian predicate uses the standard condition that every real linear combination of a finite collection has a real Gaussian law, allowing zero variance. See Gardner, [*Introduction to Random Processes with Applications to Signals and Systems*, §2.3.4](https://faculty.engineering.ucdavis.edu/gardner/wp-content/uploads/sites/146/2014/05/Introduction_to_Random_Processes_with_applications_to_Signal.pdf).

## Actual mathematical objects

All Lean declarations use namespace `Conjecture6480`; project files are in `lean/`.

| File | Role |
|---|---|
| `Conjecture6480/Processes.lean` | Actual uniform probability measure, explicit sign processes, measurable/integrable coordinates, centered Bochner covariance, joint and maximum pushforwards, exact moments, singleton probabilities and complete maximum laws |
| `Conjecture6480/Gaussian.lean` | Singleton-mass obstruction for every Mathlib `gaussianReal` law, standard linear-combination Gaussian predicate and coordinate consequence |
| `Conjecture6480.lean` | Equal covariance, distinct joint and extremal laws, non-Gaussianity, characterization of the maximum, and final existential witness theorem |
| `Check.lean` | All 12 definition printouts and 42 named theorem/instance type and transitive-axiom audits |

`μ` is the measure of `PMF.uniformOfFintype (Fin 8)` and has a proved probability-measure instance. Every needed integrability and measurability property is proved. `covarianceMatrix` uses actual centered integrals; it is not defined by a prescribed matrix. `jointLaw` and `extremeLaw` are actual measure pushforwards and have probability-measure instances. The maximum is proved to bound every coordinate and to be attained by a coordinate.

The full distributions and all covariance entries follow from the uniform PMF's measure and integration theorems by exact finite calculations. The singleton vector `(-1,-1,-1)` separates the joint laws with masses `1/8` and `0`. The real singleton `{-1}` similarly separates the maximum laws. Non-Gaussianity is proved against all means and all nonnegative variances in Mathlib's actual Gaussian law, including variance zero.

`ExplicitWitnessClaim` records the explicit finite probability-space setting and an existential over two processes, with measurability, coordinate and covariance-product integrability, both non-Gaussian properties, equal covariance, and both unequal laws. `conjecture_true` proves it using `X,Y`. Fixing this concrete space supplies a witness for the source's existence statement; it does not restrict the source's class of possible processes.

## Reproduction

Lean **4.19.0** and Mathlib **v4.19.0** are pinned. Mathlib's exact revision is `c44e0c8ee63ca166450922a373c7409c5d26b00b`; the manifest pins all transitive dependencies. From `lean/`:

```sh
lake exe cache get
lake build
lake env lean -DwarningAsError=true Conjecture6480/Processes.lean
lake env lean -DwarningAsError=true Conjecture6480/Gaussian.lean
lake env lean -DwarningAsError=true Conjecture6480.lean
lake env lean -DwarningAsError=true Check.lean
```

The optional cache supplies compiled dependencies; the submission still needs to be built. If the cache executable is unavailable, use `lake env lean --run .lake/packages/mathlib/Cache/Main.lean get`.

Run `tectonic main.tex` to reproduce the report. The package includes the Lean proof, matching LaTeX/PDF, exact bilingual source, internal semantic review and verification records. All mathematical computations occur in the Lean proof; no auxiliary numerical program is needed. Local verification and internal review are separate from official competition review and maintainer acceptance.
