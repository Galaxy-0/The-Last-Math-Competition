# Solution Review — Conjecture 00000007136 (PR 512)

**Submission:** ziangni-sys — `ziangni-sys_submission_20261004170500`  
**Reviewer:** independent competition audit  
**Date:** 2026-10-04

## Checklist

- [x] Only the permitted submission directory was added
- [x] Full LaTeX source and PDF read; independent LaTeX build passed
- [x] Lean 4.19/Mathlib c44e project independently built
- [x] Direct warning-as-error Lean check passed
- [x] No `sorry`, `admit`, `native_decide`, custom axiom, unsafe implementation, external binding, or kernel bypass
- [x] Axiom audit shows only `propext`, `Classical.choice`, and `Quot.sound`
- [x] Convex bodies, Minkowski sums, mixed areas, equality, and noncongruence match the official statement

## Counterexample

Take the full-dimensional Euclidean convex bodies

\[
K=[0,1]^2,\qquad L=[0,2]^2.
\]

For \(s,t\ge0\),

\[
sK+tL=[0,s+2t]^2,
\]

so

\[
\operatorname{area}(sK+tL)=(s+2t)^2=s^2+4st+4t^2.
\]

Thus

\[
V(K,K)=1,\qquad V(K,L)=2,\qquad V(L,L)=4,
\]

and Alexandrov–Fenchel equality holds:

\[
V(K,L)^2=2^2=1\cdot4=V(K,K)V(L,L).
\]

Nevertheless \(K\) and \(L\) are not congruent: squared distances in \(K\) are at most 2, while \(L\) contains points of squared distance 8. The squares are homothetic, but the official statement claims congruence and imposes no volume normalization or dilation quotient. Therefore its equality classification is false.

## Formal verification

Lean proves compactness, convexity, nonempty interior, the exact Minkowski-combination identity, the all-parameter area polynomial, mixed-area polarization, AF equality, transport to genuine `EuclideanSpace`, equality of coordinate and Euclidean volumes, and noncongruence over every ambient isometry. This rules out translations and orthogonal transformations as well as direct rigid motions.

Independent `lake build` and direct warning-as-error Lean checks passed. All twelve principal audits use exactly the three allowed standard axioms.

## Verdict

APPROVED — correct, non-vacuous disproof of the congruence equality condition in Conjecture 00000007136.
