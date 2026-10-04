# Solution Review — Conjecture 00000009114 (PR 544)

**Submission:** ziangni-sys — `ziangni-sys_submission_20261004174718`
**Reviewer:** independent competition reviewer (structure + build + semantic audit)
**Date:** 2026-10-04

## Checklist results
- Conjecture read: yes — the source universally claims multiplicity bounded by dimension plus one.
- Path policy: pass — only the submitter's own directory was added; clean-base metadata is unsolved/undisproved.
- LaTeX: independent `latexmk -pdf` build exited 0; the complete one-page PDF was extracted/rendered and read. Content matches the shipped Tectonic PDF.
- Lean: fresh Mathlib-pinned project built with `lake build`; exit 0. Direct `lake env lean -DwarningAsError=true Main.lean` exited 0 without warnings.
- Axioms: all ten principal theorems, including `no_bounded_subcover`, use only `[propext, Classical.choice, Quot.sound]`.
- Forbidden content: no `sorry`, `admit`, `native_decide`, extra axiom, `unsafe`, `implemented_by`, `extern`, or `skipKernelTC`.
- Auxiliary code: none needed.

## Semantic audit
Take four radius-`11/10` disks centered at `(1,0)`, `(0,1)`, `(-1,0)`, and `(0,-1)`. The origin lies in all four. Distinct centers have squared distance at least 2, exceeding `121/100`, so each disk contains its own center and no other center. Therefore any subfamily covering all centers must contain all four disks; the full family is itself a cover, so the example is non-vacuous. Its overlap multiplicity at the origin is 4, exceeding the claimed planar bound `2+1=3`.

Lean uses actual Euclidean space, metric balls, arbitrary selected subfamilies, filtered-cardinality multiplicity, exact separation and membership proofs, and negates existence of any everywhere dimension-plus-one bounded covering subfamily. The report correctly distinguishes the given-family Besicovitch formulation from fine-cover replacement variants.

## Issues found
- none blocking.

## Disposition
APPROVED — fresh LaTeX and Lean reproduction passed with only standard axioms; four indispensable planar balls force multiplicity 4 > 3, decisively refuting the stated universal n+1 bound.
