# Solution Review — Conjecture 00000003631 (PR 452)

**Submission:** feiyuceng06-prog — `feiyuceng06-prog_submission_20261004001343`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-04

## Checklist results
- Official bilingual conjecture read independently. The report quotes the English statement exactly and correctly identifies that the Chinese version makes the same numerical maximum-four assertion.
- Change policy: only the declared submission directory is added.
- LaTeX: independent `latexmk` build succeeded. The shipped and rebuilt two-page PDFs have identical extracted semantic content. One nonfatal overfull-line warning occurs on page 2 from a long theorem identifier; Ghostscript bounding-box checks show the ink remains on the page and no report content is missing.
- Lean: fresh `lake build` under Lean 4.33.1/Mathlib `0df444a3...` succeeded. Direct warning-as-error elaboration of both `Submission/Basic.lean` and `Submission.lean` also succeeded.
- Axioms: the final theorem depends only on `propext`, `Classical.choice`, and `Quot.sound`. No `sorry`, `admit`, `native_decide`, custom axiom, unsafe implementation, external implementation, or kernel bypass occurs.
- Auxiliary code: none supplied; the proof is a direct symbolic identity and requires no numerical computation.
- Base metadata marks the conjecture unsolved.

## Semantic audit
For `(P,Q)=(x²,xy)` and every nonzero linear form `L=ax+by`,
`P∂L/∂x + Q∂L/∂y = ax²+bxy=xL`.
Therefore the vector field is tangent to every line `L=0` through the origin. The five forms `x`, `y`, `x+y`, `x+2y`, and `x-y` have pairwise nonzero determinants and hence give five distinct invariant lines. Both components are homogeneous quadratic polynomials and P is nonzero, so this is an exact-degree-two system. The source imposes no nondegeneracy, general-position, coprime-component, or non-star hypothesis, so five—and indeed infinitely many— invariant lines refute the claimed maximum of four.

The Lean formalization uses actual real coefficients, the standard divisibility criterion for invariance by a line, and nonzero determinant for distinct projective lines. It proves exact quadraticity, pairwise distinctness, and all five invariance identities. The upper-bound statement is represented as nonexistence of five pairwise-distinct invariant lines, and the final theorem derives a contradiction from the constructed witness. This is non-vacuous and faithfully targets the unrestricted statement as written.

## Issues found
- Non-blocking layout: independent LaTeX compilation reports one overfull hbox on page 2 from the long identifier `conjecture_00000003631_false`. The text remains within the physical page and the complete report content is present; no mathematical or verification issue results.

## Verdict
APPROVED. This exact homogeneous quadratic system provides infinitely many—hence more than four—distinct invariant lines, and the clean Lean build proves a sufficient five-line counterexample using only standard foundational axioms.
