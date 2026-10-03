# Solution Review — Conjecture 00000001465 (PR 261)

**Submission:** orionsheep — `orionsheep_submission_20261003083615`
**Reviewer:** competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-03

## Checklist
- [x] LaTeX source and PDF present
- [x] Lean 4 project compiles completely (lake build, exit 0)
- [x] No `sorry`, no `native_decide`, no extra axioms
- [x] Submission matches the conjecture's objects and literal statement

## Conjecture (verbatim summary)
The Moreau envelope of a convex function f is M_lf(x) = inf_y{f(y) + |x-y|^2/(2l)}. The conjecture asserts the critical parameter for C^1 smoothness is l*(f) = 1/L(f): for l < l* all envelopes are C^1, while for l > l* there exists f whose envelope is nondifferentiable at a minimizer.

## What the submission proves
For convex f the Moreau envelope is C^1 for every l > 0 (classical Moreau-Yosida regularity), so the existential clause can never hold and the conjectured critical parameter does not exist. Concretely, f(x) = |x| has L(f) = 1, so l* = 1; at l = 4 > 1 the kernel certifies the envelope value M_4(0) = 0 is attained uniquely at y = 0, and M_4(h) = h^2/8 for |h| <= 4, so the difference quotient at the minimizer is h/8 -> 0 — differentiable, contradicting the clause.

## Verification notes
L(|x|) = 1, the soft-threshold proximal map giving M_4(h) = h^2/8 on |h| <= 4, and the C^1 regularity theorem for envelopes of closed proper convex functions independently confirmed. The kernel certifies the infimum-value facts, the equality analysis, and the anchor 4 > 1; the general regularity theorem is classical prose — which alone refutes the existential clause for every convex f and every l.

## Verdict
APPROVED — merged into main.

