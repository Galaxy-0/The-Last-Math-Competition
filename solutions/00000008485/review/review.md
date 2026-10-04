# Solution Review — Conjecture 00000008485 (PR 497)

**Submission:** ziangni-sys — `ziangni-sys_submission_20261004155300`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-04

## Checklist results

- **Eligibility and scope.** The three-dot diff from clean base adds only the correctly named personal submission folder. Base metadata marks conjecture 00000008485 unsolved. The copied bilingual source is byte-identical to `conjectures/00000008485.md`.
- **LaTeX and PDF.** I read the complete two-page report and all submitted source/config/log files. Fresh `latexmk -pdf` compilation succeeded (exit 0; 2 pages). I extracted and read both shipped and fresh PDF text and rendered both fresh pages with Ghostscript. No auxiliary numerical program is used.
- **Lean.** Using the official shared pinned Mathlib tree, `lake build` completed successfully. Direct `lake env lean Main.lean` also exited 0. The build and direct replay each report two harmless unused-variable linter warnings at the Dirac ergodicity proof; these do not affect proof completeness. Six central axiom audits report exactly `[propext, Classical.choice, Quot.sound]`.
- **Forbidden-content scan.** No proof escape, custom axiom, unsafe implementation, native decision shortcut, or kernel-trust override occurs.

## Semantic audit

The official definition explicitly forms the set of integration pairs over ergodic invariant probability measures and then takes its northeast Pareto boundary. It does not require full support or replace “ergodic measures” by all invariant measures.

Take the compact discrete space `X={0,1}`, identity map `T`, and continuous observables `f=(1,0)`, `g=(0,1)`. Every probability measure is invariant under the identity. An ergodic probability measure must assign the invariant singleton `{0}` measure zero or one. In the first case it is `δ0`; in the second, `{1}` has measure one and it is `δ1`. Conversely both Dirac measures satisfy the zero-one ergodicity property. Thus the ergodic measures are exactly `δ0` and `δ1`. Lean proves this classification using Mathlib's actual `Ergodic` predicate and equality of actual measures.

The Bochner integrals give `(∫f,∫g)=(1,0)` for `δ0` and `(0,1)` for `δ1`, so the integration image is exactly those two points. Neither point dominates the other, so both are Pareto-maximal and the frontier is exactly `{(1,0),(0,1)}`. Lean defines frontier maximality quantitatively over the whole image and proves this exact equality; it does not assume a frontier certificate.

The midpoint `(1/2,1/2)` is absent, so the frontier is not convex. This refutes the universal first clause. The result remains compact, as the report notes, so it isolates exactly the convexity failure. If one instead used all invariant measures or took a convex hull, this example would yield the joining segment, but that is not the definition stated in either official language.

The example is non-vacuous: the space, dynamics, observables, ergodic measures, integrals, image, and frontier are all actual mathematical objects and are completely classified. Only the first conjunct is claimed false, which suffices.

## Verdict rationale

The construction directly matches the official measure quantifier and gives a complete two-point classification. The formal proof establishes genuine ergodicity, all integrals, the full image/frontier, and Mathlib nonconvexity. Builds, replay, audits, scans, and PDF checks pass; the only warnings are non-load-bearing unused-variable notices.

## Disposition

APPROVED — ready for merge (PR 497). No merge action was taken by this reviewer.
