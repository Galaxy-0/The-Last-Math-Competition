# Solution Review — Conjecture 00000003794 (PR 430)

**Submission:** C0ldSmi1e — `C0ldSmi1e_submission_20261004084807`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-04

## Checklist results

- **Eligibility and scope.** The three-dot diff adds only the correctly named personal submission folder. Base metadata marks conjecture 00000003794 unsolved, and no prior/removed solution exists. The submitted bilingual `conjecture.md` is byte-identical to the official file.
- **LaTeX and PDF.** I read the full two-page report and all submitted source/config/verification files. A fresh `latexmk -pdf` build succeeded (exit 0; 2 pages). Text extraction, normalized comparison, and Ghostscript rendering confirmed content agreement. No auxiliary numerical program is needed.
- **Lean.** Using the shared official pinned Mathlib tree, `lake build` completed successfully. Direct strict replay of `Problem.lean`, `Conjecture3794.lean`, and `Check.lean` all exited 0. Twenty-three central axiom audits report only `[propext, Classical.choice, Quot.sound]`.
- **Forbidden-content scan.** No proof escape, custom axiom, unsafe declaration, implementation override, native decision shortcut, or kernel-trust override occurs. The only “axiom” occurrences are legitimate `#print axioms` audits.
- **Independent check.** I independently verified the five displayed solutions, matrix-vector products, rank/determinant zero, and positive semidefiniteness.

## Semantic audit

The official first substantive clause states an upper bound of `2^n` for LCP solution counts. It contains no restriction to P-matrices, nonsingular matrices, finite solution sets, or isolated solutions. The later P-matrix tightness wording is imprecise and does not supply such a domain restriction. The submission properly limits itself to refuting the unrestricted universal solution-count assertion and explicitly says its singular matrix is not a P-matrix.

Lean uses the standard orthant LCP:

`SOL(M,q)={x : x≥0, Mx+q≥0, xᵀ(Mx+q)=0}`.

It represents the nonnegative orthant by Mathlib's positive cone, uses actual matrix-vector multiplication, and proves equivalence to coordinatewise complementarity: since both vectors are nonnegative, their dot product is zero exactly when each coordinate product is zero.

Take

`M=[[1,-1],[-1,1]], q=0`.

For `x=(a,b)`, feasibility gives `a≥0`, `b≥0`, `a-b≥0`, and `b-a≥0`, hence `a=b=t≥0`. Conversely every `(t,t)` has `Mx=0`, so all LCP conditions hold. Thus the complete solution set is the ray `{(t,t):t≥0}`. Lean proves this exact classification, not merely an infinite subfamily. The map `k↦(k,k)` is injective, so the solution cardinality is genuinely infinite; its extended cardinality is infinity. In particular, the five points for `t=0,1,2,3,4` already exceed `2²=4`, and the universal bound fails at dimension two.

The matrix is nonzero, symmetric, positive semidefinite (`xᵀMx=(a-b)²≥0`), and singular. These facts are also formalized. Lean's `SolutionCountBound` quantifies over every positive dimension, every real square matrix, and every real `q`, directly matching the unrestricted count assertion in the source. The final theorem negates it by specializing to `n=2` and the displayed data.

The use of `Set.encard` is important and faithful: it represents an infinite set as infinity rather than collapsing it to a finite-valued or zero natural cardinality. Non-vacuity is direct: the LCP predicate is standard, the matrix and right-hand side are explicit, and the full solution ray is classified.

## Verdict rationale

This is a valid literal counterexample to the explicit universal solution-count clause. The submission does not overclaim a refutation of a separately restricted P-matrix version. The standard LCP formalization, complete solution classification, infinite cardinality, matrix properties, fresh builds, strict replays, and trust checks all pass.

## Disposition

APPROVED — ready for merge (PR 430). No merge action was taken by this reviewer.
