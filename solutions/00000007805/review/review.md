# Solution Review — Conjecture 00000007805 (PR 534)

**Submission:** ziangni-sys — `ziangni-sys_submission_20261004194000`  
**Reviewer:** independent competition audit  
**Date:** 2026-10-04

## Checklist

- [x] Only the permitted submission directory was added
- [x] Full LaTeX source and PDF read; independent PDF build passed
- [x] Full Lean 4.19/Mathlib c44e project independently built
- [x] Direct warning-as-error Lean check passed
- [x] No `sorry`, `admit`, `native_decide`, custom axiom, unsafe implementation, external binding, or kernel bypass
- [x] Axiom audit shows only `propext`, `Classical.choice`, and `Quot.sound`
- [x] Bodies, volumes, zero deficit, rigid motions, Hausdorff distance, and claimed exponent match the official statement

## Counterexample

In dimension one, take the compact convex bodies

\[
K=[0,1],\qquad L=[0,2].
\]

Then \(K+L=[0,3]\), so

\[
|K|=1,\quad |L|=2,\quad |K+L|=3,
\]

and the Brunn–Minkowski deficit is zero. Nevertheless no rigid motions can make the intervals close: one has length 1 and the other length 2. For any isometries \(f,g\),

\[
d_H(f(L),g(K))\ge \frac12.
\]

Indeed, nearest points in \(g(K)\) to the endpoints of the length-2 interval \(f(L)\) are at most the Hausdorff distance away, have mutual distance at most 1, and must approximate two points distance 2 apart. The triangle inequality forces \(H\ge1/2\).

Thus zero deficit does not force congruence or even arbitrarily small Hausdorff proximity. Taking \(\varepsilon_j=1/(j+1)\to0\), the claimed dimension-one bound \(C\varepsilon_j^{1/2}\) tends to zero, contradicting the uniform \(1/2\) obstruction. The submission does not overclaim normalized or homothety-quotient stability variants.

## Formal verification

Lean proves compactness, convexity, nonempty interiors, the exact Minkowski sum and volumes, zero deficit, the Hausdorff lower bound for every pair of isometries, failure of every vanishing modulus, and specifically failure of the claimed square-root power in dimension one.

Independent `lake build` and direct warning-as-error Lean checks passed. All six principal theorem audits use exactly the three allowed standard axioms.

## Verdict

APPROVED — correct, non-vacuous disproof of the unnormalized congruence-stability statement in Conjecture 00000007805.
