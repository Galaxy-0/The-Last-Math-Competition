# Solution Review — Conjecture 00000000360 (PR 424)

**Submission:** C0ldSmi1e — `C0ldSmi1e_submission_20261004064749`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-04

## Checklist results

- **Eligibility and scope.** Relative to the supplied clean base `4cc82278ba1e5becc4d20b1e2a68dede094e2b8d`, the three-dot diff adds only the correctly named personal folder `solutions/00000000360/C0ldSmi1e_submission_20261004064749/`. The base metadata marks conjecture 00000000360 unsolved. The submitted `conjecture.md` is byte-identical to the official bilingual file.
- **LaTeX and PDF.** I read the complete three-page report and all submitted source/configuration files. A fresh `latexmk -pdf` build succeeded (exit 0; 3 pages). I extracted text from both shipped and fresh PDFs, rendered every fresh page with Ghostscript, and checked the entire report, including the classical-formulation caveat. Differences are only compiler/spacing/ligature extraction artifacts; mathematical content and section order match. No auxiliary numerical program is used or required.
- **Lean.** In a fresh copied project with the official pinned Mathlib cache preseeded, `lake build` completed successfully (exit 0), and direct replay with warnings as errors succeeded for both `Conjecture360.lean` and `Check.lean` (exit 0 each). The audit prints the actual matrix product, determinant, uniform-bound, optimality, and final negation types. All eleven central axiom audits report exactly `[propext, Classical.choice, Quot.sound]`.
- **Forbidden-content scan.** No submitted `sorry`, `admit`, custom `axiom`, `native_decide`, `unsafe`, `implemented_by`, `extern`, `skipKernelTC`, or trust override occurs. The word `axioms` appears only in legitimate `#print axioms` audit lines. Toolchain and dependency revisions are pinned.
- **Author evidence.** The supplied verification and hashes match my independent build and audit; they were not treated as substitutes for replay.

## Semantic audit

The official first conjunct says that for `n=10`, `K=n!/n^n` cannot be improved for completely split diagonal forms. The written definition is homogeneous: it concerns a nonzero integer point `x` for linear forms, with no affine shifts and no requirement that every coordinate of `x` be nonzero. For coordinate-diagonal forms `L_i(x)=a_i x_i`, Lean represents exactly this situation using `Matrix.diagonal`, `Matrix.mulVec`, an actual integer vector cast to real coordinates, and Mathlib's determinant.

For every dimension `n≥2`, `e_1=(1,0,…,0)` is a nonzero integer vector. Since the second coordinate is zero, the homogeneous diagonal product contains the zero factor `L_2(e_1)`, so the absolute product equals zero. That is a global minimum because absolute values are nonnegative. Hence for every `c≥0`, every real diagonal coefficient system admits this same nonzero witness satisfying the bound. Conversely, taking the identity matrix forces any uniform constant `c` to satisfy `0≤∏x_i≤c`, hence `c≥0`. Therefore the admissible uniform constants are exactly all nonnegative real numbers, and zero is the sharp constant.

This is not caused by singular systems: if every diagonal coefficient is nonzero, Mathlib's determinant is nonzero, and the identical `e_1` witness still gives a zero product. Lean separately proves the full classification on this nonsingular subclass.

At `n=10`, `K=10!/10^10=567/1562500>0`. Since `K/2>0`, `K/2<K`, and `K/2` is uniformly valid, even a convention restricting improvements to positive constants cannot save the claimed optimality. The final Lean theorem is exactly the negation of `optimalDiagonalConstant 10 (10!/10^10)`. Non-vacuity is direct: the class includes all nonsingular real diagonal systems, the witness is explicitly nonzero, and the improved constant is explicitly positive.

The report correctly distinguishes this repository's unshifted, literal diagonal assertion from the different classical shifted Minkowski product problem. It does not rely on any external theorem. Refuting the optimality conjunct refutes the official conjunctive conjecture; the separate convex-body clause need not be false.

## Verdict rationale

The mathematical observation is elementary but decisive under the exact bilingual statement. The Lean definitions use the real diagonal matrices, determinant, integer nonzero vectors, and homogeneous products required by that statement, and the formal theorem rules out every strictly smaller nonnegative uniform constant, including the explicit positive half-constant. Fresh builds, direct replay, standard-only axiom audits, and source scans all pass.

## Disposition

APPROVED — ready for merge (PR 424). No merge action was taken by this reviewer.
