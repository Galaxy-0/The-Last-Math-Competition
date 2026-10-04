# Solution Review — Conjecture 00000008833 (PR 420)

**Submission:** ziangni-sys — `ziangni-sys_submission_20261004055331`
**Reviewer:** competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-04

## Checklist results

- Conjecture read: yes — the claim asserts an unconditional CP step-product upper bound of one; the source does not normalize `K`.
- Eligibility: base metadata is unsolved; only the properly named own submission directory is added.
- LaTeX: independent build exit 0, two US Letter pages, no unresolved references or substantive warnings; shipped and fresh content match.
- Lean: official shared pinned dependencies linked; `lake build` exit 0 and direct warnings-as-errors elaboration exit 0.
- Axioms: only `[propext, Classical.choice, Quot.sound]`.
- Forbidden content: none in source.
- Auxiliary programs: none needed.

## Semantic audit

For the real scalar problem `f(x)=g(x)=x²/2`, nonzero coupling `Kx=x/4`, and steps `τ=σ=2`, the proved proximal maps are `a/3`. The actual CP update with `θ=1` is `y'=(y+\bar x/2)/3`, `x'=(x-y'/2)/3`, and `\bar x'=-x/3-y'/3`. If `M` is the maximum absolute coordinate, every new coordinate is at most `M/2`, so every initial state converges geometrically to the proved saddle `(0,0)`. Yet `τσ=4>1`. The Lean proof uses a real bounded self-adjoint coupling map, proper continuous convex objectives, the genuine Fenchel supremum, unique global proximal minimizers, actual function iteration, and product-topology convergence for all states. It is consistent with the standard operator-scaled condition because `τσ||K||²=1/4`. Thus the official unqualified numerical product bound is false as stated.

## Verdict

APPROVED — the fully formal all-state convergence counterexample is mathematically sound and every independent reproduction check passes.
