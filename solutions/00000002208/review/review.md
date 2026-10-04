# Solution Review — Conjecture 00000002208 (PR 480)

**Submission:** ziangni-sys — `ziangni-sys_submission_20261004150700`
**Reviewer:** independent competition reviewer (structure + build + semantic audit)
**Date:** 2026-10-04

## Checklist results
- Conjecture read: yes — the official statement claims a Puiseux monoid is atomic iff its generator ℤ-rank is at least 2. The included source is byte-identical to the official bilingual file.
- Path policy: pass — only the submitter's own solution directory was added; clean-base metadata is unsolved and undisproved.
- LaTeX: fresh `latexmk -pdf` build exited 0 after two passes, with one complete page and no errors. I read the entire report and extracted/rendered the PDF independently. It matches the shipped Tectonic PDF in content.
- Lean: pinned Lean 4.19/Mathlib project independently built with `lake build`; exit 0. Direct `lake env lean -DwarningAsError=true Main.lean` exited 0.
- Axioms: all six principal results, including `counterexample`, use only `[propext, Classical.choice, Quot.sound]`.
- Forbidden content: no `sorry`, `admit`, `native_decide`, extra axiom, `unsafe`, `implemented_by`, `extern`, or `skipKernelTC`.
- Auxiliary code: none shipped or needed.

## Semantic audit
The counterexample is `M=⟨1,2⟩⊆ℚ_{≥0}=ℕ`. It is a real Puiseux monoid. Its only unit is zero; `1` is an atom because no two positive natural numbers sum to `1`; and every natural number `n`, including zero via the empty sum, is a finite sum of `n` copies of this atom. Thus `M` is atomic. The actual integer span of the generators is `ℤ·1`, which has rank `1`, refuting the claimed necessity of rank at least `2`.

The Lean proof matches this argument structurally: actual additive-submonoid closure, proved carrier equality, actual atom decompositions, finite factorizations, and actual `Module.rank` transported through an explicit ℤ-linear equivalence. The example is non-vacuous and no unofficial restriction is needed. Redundancy in the generator list is not forbidden by the bilingual statement, so this decisively disproves the universal criterion.

## Issues found
- none blocking.

## Disposition
APPROVED — independent LaTeX and Lean builds passed, only standard axioms occur, and the formal theorem supplies a genuine atomic Puiseux monoid whose generator span has rank one, refuting the conjecture's necessity direction.
