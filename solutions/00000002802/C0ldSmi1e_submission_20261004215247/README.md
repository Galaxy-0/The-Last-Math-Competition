# Disproof of conjecture 00000002802

The fair Bernoulli probability law is a nondegenerate lattice law with every exponential moment. Its actual Cramér convex dual equals

\[
I(x)=\log 2+x\log x+(1-x)\log(1-x),\qquad 0<x<1,
\]

and is smooth on this nonempty interval. This contradicts the claimed necessary implication from interior twice differentiability to a non-lattice underlying law. It suffices to disprove the criterion in both language versions, without assigning a meaning to the additional variance-functional or periodic-correction phrases.

## Reproduction

`main.tex` and `main.pdf` give the mathematical argument. `conjecture.md` is the exact bilingual source. The complete Lean project is in `lean/`, pinned to Lean 4.19.0 and Mathlib v4.19.0; `lake-manifest.json` fixes all nine dependency revisions.

From `lean/`, with the pinned Lean toolchain installed:

```sh
lake exe cache get
lake build
lake env lean -DwarningAsError=true Conjecture2802/Law.lean
lake env lean -DwarningAsError=true Conjecture2802/Formula.lean
lake env lean -DwarningAsError=true Conjecture2802/Transform.lean
lake env lean -DwarningAsError=true Conjecture2802/Regularity.lean
lake env lean -DwarningAsError=true Conjecture2802.lean
lake env lean -DwarningAsError=true Check.lean
```

The default build imports every implementation module. `Check.lean` prints all 13 definitions and the types and transitive axiom dependencies of all 48 theorems and the named probability instance. No auxiliary numerical, simulation or symbolic program supplies any mathematical step. The report can be rebuilt with `tectonic main.tex`.

## Correspondence with the source

- `Law.lean` constructs the actual measure `(1/2) • dirac 0 + (1/2) • dirac 1`, proves it is a probability measure, its atom masses, nondegeneracy, all exponential moments and membership in the arithmetic lattice with offset 0 and positive spacing 1. Its moment and cumulant generating functions come from the library integral.
- `Formula.lean` proves an upper bound for every dual objective by logarithm concavity and proves equality at `log x - log (1-x)`. The closed form is an auxiliary function until its equality with the actual supremum is proved.
- `Transform.lean` defines the extended-real convex dual using exactly the exponential-integrability parameters. This avoids the library's totalized nonintegrable real integral. For this law every real parameter is integrable. The exact supremum equals the finite expression on `(0,1)` and equals positive infinity outside `[0,1]`. The rate of any probability law is nonnegative.
- `Regularity.lean` proves `ContDiffOn ℝ ∞` of the finite real representative. It provides the sufficient bridge from a C² representative to actual twice differentiability on an open set, explicitly requiring differentiability of both the function and its ordinary derivative. It does not equate C² and mere twice differentiability for arbitrary functions or use totalized `EReal.toReal` at infinity.
- `Conjecture2802.lean` supplies `explicit_counterexample` and `necessary_criterion_fails_all_three_readings`. The latter combines the negations of the necessary non-lattice implication for each of three explicitly distinguished interiors. The universal wrappers retain probability, all exponential moments and nondegeneracy; restricting to this strong subclass makes a necessary universal consequence weaker, and the counterexample still refutes it.

Ordinary topological support is `{0,1}` and has empty real interior; the literal differentiability assertion there is vacuous. Convex support is `[0,1]` and has nonempty interior `(0,1)`, where the smoothness result is substantive. The effective domain `D = {x | I(x) < +∞}` satisfies `(0,1) ⊆ D ⊆ [0,1]`, so its interior is also `(0,1)`. No endpoint values or equality of the full effective domain with `[0,1]` are claimed. Ordinary support is never silently replaced by convex support.

Both the English equivalence and either natural grouping of the Chinese variance clause imply that twice differentiability requires a non-lattice law. The proven lattice witness contradicts this consequence. The submission does not separately settle the converse, the unspecified variance functional or a periodic correction, and does not claim to formalize an independent-sum process or the full large-deviation principle. Its formal scope is the actual convex dual explicitly named by the source.

`VERIFICATION.md` records the independent execution, matching report/PDF, eligibility and package checks. `SEMANTIC_REVIEW.md` records a separate source-level review by an agent who authored none of the submitted proof or report. These are local checks and independent internal scrutiny; maintainer acceptance is a separate decision. `verification/SHA256SUMS.json` covers every submitted file except itself.
