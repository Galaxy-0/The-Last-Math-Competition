# Solution Review — Conjecture 00000007801 (PR 531)

**Submission:** ziangni-sys — `ziangni-sys_submission_20261004171753`
**Reviewer:** independent competition reviewer (structure + build + semantic audit)
**Date:** 2026-10-04

## Checklist results
- Conjecture read: yes — the official formula asserts `G_k(K)≤binom(d,k)V(S)` for a standard simplex S, with no normalization of K.
- Path policy: pass — only the submitter's own directory was added; clean-base metadata is unsolved/undisproved.
- LaTeX: independent `latexmk -pdf` build exited 0; both pages extracted/rendered and read. Content matches the shipped Tectonic PDF.
- Lean: fresh Mathlib-pinned project built with `lake build`; exit 0. Direct `lake env lean -DwarningAsError=true Main.lean` exited 0 without warnings.
- Axioms: all ten principal theorems, including `counterexample`, use only `[propext, Classical.choice, Quot.sound]`.
- Forbidden content: no `sorry`, `admit`, `native_decide`, extra axiom, `unsafe`, `implemented_by`, `extern`, or `skipKernelTC`.
- Auxiliary code: none needed.

## Semantic audit
For `K=[0,2]` in real dimension one, the complete vertex set is `{0,2}`. The only unordered two-vertex subset has convex hull `[0,2]`, so `G₁(K)=2`. The standard one-simplex `[0,1]` has volume 1, making the displayed right side `binom(1,1)·1=1`; thus the claimed `2≤1` is false. The source's explicit coefficient also evaluates to 1/2 and yields the same false bound after multiplying by `V(K)=2`.

Lean uses the actual real interval, proves compactness/convexity/nonempty interior/ambient dimension, classifies all extreme points, exhaustively enumerates the vertices and their sole two-element subset, forms the actual convex hull, computes actual Lebesgue volumes and finite mean, and negates both displayed inequalities. The example is non-vacuous and the report honestly confines it to the stated formula rather than a normalized classical variant.

## Issues found
- Nonblocking degeneracy/scope flag: dimension one is very small and dilation immediately exposes the formula's missing normalization, but neither official language excludes d=1 or dilates/normalizes K. This makes the literal displayed universal inequality false.

## Disposition
APPROVED — fresh LaTeX and Lean reproduction passed with only standard axioms; the formal complete vertex-volume computation gives `G₁([0,2])=2` versus displayed bound 1, decisively refuting the stated formula.
