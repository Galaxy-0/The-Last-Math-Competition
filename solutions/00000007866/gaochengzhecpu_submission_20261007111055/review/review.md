# Solution Review — Conjecture 00000007866 (PR 837)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261007111055`
**Reviewer:** independent competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-07

## Checklist results
- Conjecture read: yes — the source defines `D_n = sup |S_n mod 1 − n/2|` and asserts `D_n = O((log n)^{1/2})`, with an `O(1)` bound of constant `1/4` for transcendental-step sequences.
- Change scope: only `solutions/00000007866/gaochengzhecpu_submission_20261007111055/` was added; the conjecture is unsolved in the base metadata.
- LaTeX: `main.tex` read in full.
- Lean build: Lean 4.19.0, Mathlib `c44e0c8ee63ca166450922a373c7409c5d26b00b`. Independent fresh `lake build` exit 0; direct `lake env lean -DwarningAsError=true Main.lean` exit 0.
- Forbidden content: none.
- Auxiliary code: none required.
- Axioms: standard three only.

## Semantic audit
Reading `S_n mod 1` as the fractional part `{S_n} ∈ [0,1)`, we have `|{S_n} − n/2| ≥ n/2 − {S_n} > n/2 − 1`, so `D_n > n/2 − 1` grows linearly. This contradicts both `O((log n)^{1/2})` and any eventual `O(1)` bound (in particular `1/4`). The obstruction holds pointwise for every real trajectory, so no probabilistic or rounding assumption can reverse it.

The Lean project defines `deviation` via the actual `Int.fract` and absolute value, `maximalDeviation` as the actual real supremum `sSup`, proves the linear lower bound, and negates the actual `Asymptotics.IsBigO` statements at `atTop` for `Real.sqrt (Real.log n)` and the constant `1` in `every_maximum_violates_both_bounds`. `quarter_bound_fails` shows the `1/4` constant fails at `n = 3`. The displayed expression is not replaced by a sum of fractional parts or by star discrepancy.

## Issues found
- The disproof addresses the literal displayed definition (fractional part of `S_n`). Under that reading, the asserted growth is impossible. The submission is explicit that it does not assess any reformulation.

## Verdict rationale
The literal growth claim of the conjecture is false, and the Lean formalization rigorously establishes the linear lower bound and the failure of both `IsBigO` claims with only the standard axioms.

## Disposition
APPROVED — ready to merge (PR 837).
