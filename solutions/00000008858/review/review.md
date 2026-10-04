# Solution Review — Conjecture 00000008858 (PR 439)

**Submission:** ziangni-sys — `ziangni-sys_submission_20261004094546`  
**Reviewer:** independent competition audit  
**Date:** 2026-10-04

## Checklist

- [x] Only the permitted submission directory was added; conjecture and metadata untouched
- [x] LaTeX source and shipped PDF present; full source and PDF read
- [x] Independent LaTeX build passed and reproduced the report content
- [x] Full Lean project independently built; direct warning-as-error Lean check passed
- [x] No `sorry`, `admit`, `native_decide`, extra axiom, unsafe/foreign implementation, or kernel bypass
- [x] Axiom audit shows only `propext`, `Classical.choice`, and `Quot.sound`
- [x] Formal objects are non-vacuous and match the official conjecture

## Conjecture and counterexample

The conjecture asserts, in its first universal clause, that alternating orthogonal projections between two closed convex sets always converge weakly to a nearest point in their intersection. The submission uses the real Euclidean halfspaces \(A=\{(s,t):t\ge0\}\) and \(B=\{(s,t):s\le t\}\), which are closed, convex, and have nonempty intersection.

Their genuine metric projections are

\[
P_A(s,t)=(s,\max(0,t)),\qquad
P_B(s,t)=
\begin{cases}
(s,t),&s\le t,\\
((s+t)/2,(s+t)/2),&s>t.
\end{cases}
\]

From \(x_0=(2,-1)\), alternating projection onto \(A\) and then \(B\) gives

\[
(2,-1)\xrightarrow{P_A}(2,0)\xrightarrow{P_B}(1,1),
\]

and \((1,1)\) is fixed by both projections. Thus the sequence strongly (therefore weakly) converges to \((1,1)\). But \((1/2,1/2)\) also lies in \(A\cap B\), and

\[
\|x_0-(1/2,1/2)\|^2=9/2<5=\|x_0-(1,1)\|^2.
\]

Therefore the actual weak limit is not a nearest intersection point, disproving the universal nearest-point assertion.

## Formal verification

The Lean project uses Mathlib’s actual `EuclideanSpace ℝ (Fin 2)`, its Euclidean norm and metric, not a private surrogate. It proves:

- both sets are closed and convex;
- both projection maps minimize distance to every point of the relevant set, for every input;
- the first projections, fixed points, and every later iterate of the complete-cycle recursion;
- strong and weak convergence of the complete-cycle sequence;
- weak-limit uniqueness using the standard all-continuous-linear-functionals definition and coordinate functionals;
- strict proximity of \((1/2,1/2)\) over \((1,1)\);
- no point can be both a weak limit and a nearest intersection point.

The individually indexed alternating orbit is also proved to alternate the actual projections by parity and satisfies the same obstruction. This rules out a reinterpretation based only on complete-cycle indexing.

## Independent reproduction

Independent `latexmk` compilation succeeded. `lake build` and `lake env lean -DwarningAsError=true Main.lean` both exited 0. The printed axiom audits for all principal projection, convergence, orbit, and counterexample theorems list exactly `propext`, `Classical.choice`, and `Quot.sound`. No incomplete-proof or computation-trust token is present.

## Verdict

APPROVED — this is a correct, non-vacuous disproof of Conjecture 00000008858.
