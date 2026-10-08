# Conjecture 00000007866: the stated fractional-part deviation grows at least linearly

For every real trajectory S, the quantity |fract(S_n)-n/2| is greater than n/2-1. A supremum over any nonempty family of trajectories obeys the same lower bound. It cannot be O(sqrt(log n)) or O(1), irrespective of step values, random rounding, or independence. This addresses the formula actually displayed in the source.

## Files and reproduction

- `main.tex`, `main.pdf`: full disproof with scope and formal correspondence.
- `SOURCE.md`: the exact original bilingual source bytes.
- `lean/`: portable project pinned to Lean 4.19.0 and Mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`.
- `verification/`: fresh build logs, axiom output, hashes, source provenance, and reviews.

Inside `lean/`, run `lake build` and `lake env lean -DwarningAsError=true Main.lean`. On a new machine, `lake exe cache get` retrieves official dependency artifacts. The manifest pins all dependencies; the submitted configuration has no local paths. Run `tectonic main.tex` from the submission directory to reproduce the PDF. No auxiliary numerical experiment is needed.

## Formalization and scope

`deviation` uses actual `Int.fract` and real absolute value. `maximalDeviation` is the actual real supremum `sSup` of all deviations in an arbitrary nonempty sample space. The range is proved bounded above and its supremum is proved to dominate every trajectory. The linear lower bound is proved from the genuine fractional-part range theorem.

`every_maximum_violates_both_bounds` negates the actual `Asymptotics.IsBigO` statements at `Filter.atTop` for `Real.sqrt (Real.log n)` and the constant one. It works for every real-valued trajectory family, thus for any random-walk realization as a special case. No invented rounding model or surrogate numerical growth statistic is used. The theorem does not need probability assumptions because the obstruction holds pointwise for every outcome.

The constant 1/4 fails already at n=3 and no eventual constant bound is possible. The exact dyadic integer partial-sum identity is included only as an illustration, not as a zero-error substitute for the source's probabilistic hypotheses. The source's fractional-part formula is not replaced by a sum of fractional parts, a normalized quantity, or star discrepancy.

Fresh builds use only official unmodified dependency artifacts at their pinned commits, and compile this submission in a new directory without its previous artifacts. The audit excludes proof gaps, custom axioms, and native computation shortcuts. The built-in LaTeX compiler is attempted and its actual result recorded; Tectonic exports the PDF and every page is inspected. Author and parent-agent adversarial reviews are separate; no external independent review is claimed.
