# Solution Review — Conjecture 00000000603 (PR 412)

**Submission:** jilint777 — `jilint777_submission_20261004045347`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-04

## Checklist results

- Full bilingual conjecture read. Base metadata marks the conjecture unsolved. The PR adds only its own solution directory.
- Read the complete LaTeX report and all four PDF pages. Fresh two-pass `pdflatex` compilation exited 0; rendered pages are complete. Shipped/rebuilt PDF text differs only in old PDF font/glyph extraction artifacts, not mathematical content.
- Fresh self-contained Lean 4.19.0 project: `lake build` exited 0, and direct `lake env lean Main.lean -DwarningAsError=true` exited 0.
- No forbidden proof shortcut. The principal theorems use at most `propext` and `Quot.sound`; exact arithmetic theorems use no axioms. `decide +kernel` is kernel checking, not `native_decide`.
- Ran `verify.py`: exit 0, all internal assertions and checks passed. Independently recomputed the closed-form coefficient values with a separate Python calculation.
- No additional auxiliary source exists.

## What is proved

The Conway polynomials of odd two-strand torus knots are determined by the standard skein recursion for closures of `σ₁^n`. For `T(2,2k+1)`,

`∇(z) = Σ_{i=0}^k C(k+i, 2i) z^(2i)`.

For `T(2,25)` (`k=12`), the even coefficients are

`1, 78, 1001, 5005, 12870, 19448, 18564, …`

so the peak is coefficient index 5 (`z^10`), not predicted index 6. The coefficient at predicted position 6 is smaller under both exponent and even-index interpretations.

For `T(2,61)` (`k=30`), the predicted floor is 15. The unique maximum is at `z^26`, with value `C(43,26)=421171648758`; `[z^15]=0`, `[z^28]=416714805914`, and `[z^30]=344867425584`. Thus the peak clause fails under every reasonable indexing convention.

Lean proves uniqueness of the skein recursion solution, consistency of the computed family, exact coefficients, the unique peak of `T(2,61)`, and failure of `PeakClaim` for exponent, zero-based even, and one-based even position readings. Python independently derives the same polynomials through the classical Alexander-polynomial formula and surveys all coprime `T(p,q)` with `p<q≤30`; my separate closed-form recomputation confirms the decisive values.

## Verdict rationale

The universal torus-knot peak-location law is decisively false at the explicit genuine torus knot `T(2,25)`, and `T(2,61)` excludes indexing ambiguity. The coefficient derivation is mathematically correct, independently checked through two routes, and kernel-verified. Refuting one asserted conjunct is sufficient to refute the conjecture.

**Disposition: APPROVED.**
