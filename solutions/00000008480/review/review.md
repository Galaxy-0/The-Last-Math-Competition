# Solution Review — Conjecture 00000008480 (PR 410)

**Submission:** ziangni-sys — `ziangni-sys_submission_20261004051119`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-04

## Checklist results

- Full bilingual conjecture read. Base metadata marks the ID unsolved; the PR adds only its own directory.
- Full report and both shipped PDF pages read. Fresh two-pass `pdflatex` compile exited 0; rebuilt and shipped PDFs have the same two-page mathematical content, with only compiler-specific text-extraction artifacts.
- Lean 4.19.0 with pinned Mathlib `c44e0c8ee63ca166450922a373c7409c5d26b00b`. Full `lake build` exited 0 (`[2163/2164] Built Main`); direct warning-as-error Lean check exited 0.
- No forbidden proof shortcut. All six principal theorems use only `propext`, `Classical.choice`, and `Quot.sound`.
- No auxiliary computation is required.

## Counterexample

Use the compact one-point probability system with Dirac measure, identity map, and continuous observable `f=0`. It is ergodic. Let the unbounded nonnegative driver be `h_i=i`.

For the conjecture's displayed origin-zero average,

`sup_x (1/n) Σ_{i=0}^{n-1} (f(T^i x)+h_i)`

has only one possible value and equals

`(1/n) Σ_{i=0}^{n-1} i = (n-1)/2`.

Therefore the optimized average divided by `n` tends to `1/2`, not zero, so the supremum is linear rather than sublinear. The submission proves the stronger formula `k+(n-1)/2` for every fixed window origin `k`, with ratio still tending to `1/2`.

The Lean model uses the actual Euclidean-free compact `Unit`, Dirac probability measure, identity map, Mathlib `Ergodic`, map iterates, finite sums, and `sSup` over the actual initial-state range. It proves the singleton range, derives the arithmetic formula, proves the ratio limit, and negates Mathlib's `IsLittleO`. This directly refutes the universal unbounded-driver sublinear clause in both source languages.

**Disposition: APPROVED.**
