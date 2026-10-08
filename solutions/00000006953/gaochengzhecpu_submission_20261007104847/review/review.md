# Solution Review — Conjecture 00000006953 (PR 835)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261007104847`
**Reviewer:** independent competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-07

## Checklist results
- Conjecture read: yes — the source asserts that the optimal stratified-sampling allocation has proportions equal to the stratum variances.
- Change scope: only `solutions/00000006953/gaochengzhecpu_submission_20261007104847/` was added; the conjecture is unsolved in the base metadata.
- LaTeX: `main.tex` read in full.
- Lean build: Lean 4.19.0, Mathlib `c44e0c8ee63ca166450922a373c7409c5d26b00b`. Independent fresh `lake build` exit 0; direct `lake env lean -DwarningAsError=true Main.lean` exit 0.
- Forbidden content: none.
- Auxiliary code: `verify.py` re-run — PASS (exact enumeration of all 32 outcomes with rational arithmetic).
- Axioms: standard three only.

## Semantic audit
With two equal-weight strata (values `±1` and `±2`, variances `1` and `4`), equal costs, and five observations, the variance-proportional allocation is `(1,4)` with variance `Var(T_{1,4}) = (1/4)(1/1 + 4/4) = 1/2`. The competing admissible allocation `(2,3)` uses the same total count and has `Var(T_{2,3}) = (1/4)(1/2 + 4/3) = 11/24 < 1/2`. Hence variance-proportional allocation is not optimal. The Lean project builds a genuine probability space (the 32-point product measure `(1/32)·count`, proved to be a probability measure), defines the estimators and `Optimal` via the actual `ProbabilityTheory.variance`, and proves the exact variances `1/2` and `11/24` and `variance_proportional_allocation_not_optimal : ¬ Optimal 1`. No variance is assigned by definition.

## Issues found
none blocking.

## Verdict rationale
The counterexample is correct, non-vacuous, and fully formalized with only the standard axioms; the report and the Lean statements agree.

## Disposition
APPROVED — ready to merge (PR 835).
