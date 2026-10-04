# Solution Review — Conjecture 00000008800 (PR 516)

**Submission:** ziangni-sys — `ziangni-sys_submission_20261004174000`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-04

## Checklist results
- Official bilingual conjecture read independently; the report correctly targets its explicit variance scaling clause.
- Change policy: only the declared submission directory is added.
- LaTeX: independent `latexmk` build succeeded. Shipped and rebuilt two-page PDFs have identical extracted semantic content and no TeX warnings.
- Lean: official pinned dependencies were linked; fresh `lake build` and direct `lake env lean -DwarningAsError=true Main.lean` succeeded under Lean 4.19.0/Mathlib `c44e0c8e...`.
- Axioms: all ten printed results depend only on `propext`, `Classical.choice`, and `Quot.sound`. No `sorry`, `admit`, `native_decide`, custom axiom, unsafe implementation, external implementation, or kernel bypass occurs.
- Auxiliary programs: none supplied or needed; the probability construction and all m are handled symbolically.
- Base metadata marks the conjecture unsolved.

## Semantic audit
For the unbiased trace estimator based on `A=diag(1,0)` and a uniform diagonal seed, one sample equals 2 or 0 with equal probability. Its expectation is trace(A)=1 and its variance is 1. Averaging m independent seeded repetitions preserves unbiasedness and gives variance `1/m`. Hence its variance divided by the conjectured reciprocal-root scale `1/√m` is `1/√m`, which tends to 0. Thus the variance is not equal to, bounded below by, or asymptotically of order `1/√m`; it is one order smaller. The source explicitly says variance rather than standard deviation, so this distinction is not an ambiguity. The example is a genuine nondegenerate randomized benchmark, and the proof does not depend on denying the separate Bernoulli-concentration clause.

Lean formalizes the seed PMF, matrix sampling, product probability space, independent coordinates and outputs, identical distributions, unbiasedness, exact variance for every positive repetition count, ratio convergence, and negation of every eventual positive `c/√m` lower bound. This is substantially stronger than checking a finite repetition count.

## Issues found
None blocking.

## Verdict
APPROVED. The exact randomized trace benchmark has variance `1/m`, decisively refuting the conjectured reciprocal-root variance law, with all independent checks passing.
