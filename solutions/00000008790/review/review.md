# Solution Review — Conjecture 00000008790 (PR 482)

**Submission:** ziangni-sys — `ziangni-sys_submission_20261004150322`
**Reviewer:** independent competition reviewer (structure + build + semantic audit)
**Date:** 2026-10-04

## Checklist results
- Conjecture read: yes — the final clause universally asserts feasibility of pairwise negatively correlated rounding over every down-closed constraint family.
- Path policy: pass — only the submitter's own new directory was added; clean-base metadata is unsolved/undisproved.
- LaTeX: fresh `latexmk -pdf` build exited 0 after two passes; both pages extracted/rendered and read. Content matches the shipped Tectonic PDF.
- Lean: pinned Lean 4.19/Mathlib project independently built with `lake build`; exit 0. Direct `lake env lean -DwarningAsError=true Main.lean` exited 0.
- Axioms: all nine principal results, including `counterexample`, use only `[propext, Classical.choice, Quot.sound]`.
- Forbidden content: no `sorry`, `admit`, `native_decide`, extra axiom, `unsafe`, `implemented_by`, `extern`, or `skipKernelTC`.
- Auxiliary code: none needed; probabilities and inequalities independently recomputed.

## Semantic audit
The counterexample uses the down-closed family `|S|≤1` on `{1,2}`, fractional point `(1/2,1/2)`, and masses `1/8,3/8,3/8,1/8` on `00,01,10,11`. Marginals are exactly `1/2`; selected-pair and complementary-zero joint probabilities are `1/8`, strictly below the product `1/4`; hence pairwise negative correlation holds. But the infeasible set `{1,2}` occurs at `11` with probability `1/8`, so feasibility is not almost sure.

Lean builds the actual PMF/probability measure, actual coordinate indicators and selected sets, actual down-closed family and LP inequalities, and evaluates the actual infeasible event. This decisively refutes the universal sufficiency claim. The report correctly does not claim anything about a concrete constraint-aware pipage algorithm or the conjecture's other clauses.

## Issues found
- none blocking.

## Disposition
APPROVED — independent PDF and Lean builds passed with only standard axioms, and the formal distribution gives a genuine marginal-preserving, pairwise-negatively-correlated rounding that is infeasible with positive probability.
