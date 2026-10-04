# Solution Review — Conjecture 00000008590 (PR 486)

**Submission:** ziangni-sys — `ziangni-sys_submission_20261004151500`
**Reviewer:** independent competition reviewer (structure + build + semantic audit)
**Date:** 2026-10-04

## Checklist results
- Conjecture read: yes — the source claims minimal positive completion is unique iff the missing block is at a corner.
- Path policy: pass — only the submitter's own directory was added; clean-base metadata is unsolved/undisproved.
- LaTeX: fresh `latexmk -pdf` build exited 0; the complete one-page PDF was extracted/rendered and read. Content matches the shipped Tectonic PDF.
- Lean: fresh Mathlib-pinned build with `lake build` exited 0; direct `lake env lean -DwarningAsError=true Main.lean` exited 0 without warnings.
- Axioms: all six principal theorems, including `counterexample`, use only `[propext, Classical.choice, Quot.sound]`.
- Forbidden content: no `sorry`, `admit`, `native_decide`, extra axiom, `unsafe`, `implemented_by`, `extern`, or `skipKernelTC`.
- Auxiliary code: none needed.

## Semantic audit
In the 3×3 layout with every specified scalar block zero except the central `(1,1)` entry, zero is a positive completion. It uniquely minimizes operator norm because zero is the global lower norm and only the zero operator has norm zero. It is least in Loewner order because every feasible completion is positive. Any Loewner-minimal feasible `T` must also satisfy `T⪯0`; positivity then makes every `⟨x,Tx⟩=0`, and self-adjointness/polarization proves `T=0`. Lean formalizes actual Euclidean-space continuous operators, inner-product entries, positivity, both minimality quantifications, and non-corner status.

This gives unique norm-minimal and unique Loewner-minimal positive completions at a central missing block, refuting necessity in the corner-uniqueness law. The all-zero specified data are permitted by the literal bilingual statement; the report openly notes the degeneracy and does not claim anything about the other conjuncts.

## Issues found
- Nonblocking degeneracy flag: the counterexample uses all-zero specified blocks. No nondegeneracy hypothesis appears in either official language, so this is valid against the literal universal claim.

## Disposition
APPROVED — independent LaTeX and Lean reproduction passed with only standard axioms; the formal central-block example proves unique minimality under both standard interpretations and decisively refutes the conjecture's corner-uniqueness clause.
