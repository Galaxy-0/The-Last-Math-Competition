# Solution Review — Conjecture 00000008818 (PR 529)

**Submission:** ziangni-sys — `ziangni-sys_submission_20261004183500`
**Reviewer:** independent competition review (optimization, BFGS algebra, build)
**Date:** 2026-10-04

## Checklist
- [x] Official bilingual conjecture read; universal superlinear-convergence conjunct identified
- [x] Full LaTeX source and two-page PDF read; independent PDF builds passed
- [x] Full Lean project independently rebuilt
- [x] Direct elaboration passed; only a non-substantive style warning noted
- [x] Only standard foundational axioms reported
- [x] No auxiliary program shipped; BFGS orbit independently recomputed
- [x] No incomplete-proof marker, native decision tactic, custom axiom, unsafe construct, external hook, or kernel bypass
- [x] Submission adds only its own correctly named folder
- [x] Conjecture unsolved and no earlier PR found

## Counterexample
Let \(f(x)=x^4\), a \(C^\infty\) strictly convex function with unique minimizer \(0\) and degenerate Hessian \(f''(0)=0\). Choose \(r\in(0,1)\) satisfying \(r^3+r^2=1\), and set

\[
x_n=r^n,\qquad B_n=\frac{4x_n^2}{1-r}>0.
\]

The BFGS direction is \(p_n=(r-1)x_n\), so \(x_{n+1}=r^{n+1}\). The secant equation and full scalar Hessian BFGS update both hold exactly. Every unit step is descending and satisfies Armijo with \(c_1=1/100\) and strong Wolfe with \(c_2=9/10\).

Nevertheless,

\[
\frac{|x_{n+1}|}{|x_n|}=r\approx0.754877666
\]

for every \(n\), so the convergence is only linear. This refutes universal Q-superlinear convergence for smooth convex problems.

## Scope
The example does not assert strong convexity or a positive Hessian at the minimizer. It refutes the source's unqualified smooth-convex universality claim, not nondegenerate BFGS theorems. The separate stochastic clause is not needed once the first conjunct is false.

## Formal audit
Lean proves smoothness, the actual derivative, strict convexity, unique minimization, vanishing Hessian, existence and bounds for \(r\), positivity of all Hessian estimates, the secant identity, the complete scalar BFGS update, Armijo and strong-Wolfe acceptance, convergence, and non-vanishing of the actual error ratio. A fresh `lake build` succeeded. All printed theorems use only `propext`, `Classical.choice`, and `Quot.sound`.

## Documentation
The shipped and independently XeLaTeX-compiled PDFs have identical normalized extracted text; pdfLaTeX also succeeded. A non-substantive Lean style warning is recorded but does not affect the proof.

## Verdict
APPROVED — ready for integration.
