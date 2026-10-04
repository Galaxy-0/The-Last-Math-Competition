# Solution Review — Conjecture 00000008829 (PR 528)

**Submission:** ziangni-sys — `ziangni-sys_submission_20261004182000`
**Reviewer:** independent competition review (optimization, Lean semantics, build)
**Date:** 2026-10-04

## Checklist
- [x] Official bilingual conjecture read and preserved byte-for-byte
- [x] Full LaTeX source and one-page PDF read; independent PDF builds passed
- [x] Full Lean project independently rebuilt
- [x] Direct Lean elaboration passed; only a non-substantive style warning noted
- [x] Only standard foundational axioms reported
- [x] No auxiliary program shipped; exact trajectory independently recomputed
- [x] No incomplete-proof marker, native decision tactic, custom axiom, unsafe construct, external hook, or kernel bypass
- [x] Submission adds only its own correctly named folder
- [x] Conjecture unsolved in base metadata

## Counterexample
Minimize \(x^2/2\) subject to \(x\ge0\), with the indexed constraint \(c_1(x)=-x\). The unique minimizer is \(0\), where this constraint is active.

Projected gradient with step \(1/2\) from \(x_0=1\) uses the genuine projection \(P_{[0,\infty)}(y)=\max(0,y)\). Since every iterate is nonnegative,

\[
x_{k+1}=P_C(x_k-\tfrac12x_k)=x_k/2,
\]

so \(x_k=2^{-k}>0\) and \(x_k\to0\). Nevertheless,

\[
I(x_k)=\varnothing\quad\text{for every finite }k,
\qquad
I(0)=\{1\}.
\]

Thus no finite time is reached after which the active set agrees with the solution's active set.

## Semantic conclusion
The conjecture asserts finite active-set identification without an algorithm or nondegeneracy hypothesis. The example uses a strongly convex smooth objective, a closed convex feasible set, a safe projected-gradient step, and a convergent feasible trajectory, yet never identifies the boundary constraint. This refutes the unqualified identification conjunct. The failure is caused by lack of strict complementarity, as the report transparently explains.

## Formal audit
Lean formalizes the actual objective, gradient, strong quadratic identity, closed convex feasible set, unique constrained minimizer, metric-projection inequality, projected-gradient update, exact iterates, convergence, indexed active sets, and nonexistence of finite identification. Fresh `lake build` succeeded. Direct elaboration passed; all printed theorems use only `propext`, `Classical.choice`, and `Quot.sound`.

## Documentation
The shipped and independently XeLaTeX-compiled one-page PDFs have identical normalized extracted text. Independent pdfLaTeX compilation also succeeded. A non-substantive Lean style-linter warning is recorded but does not affect the proof.

## Verdict
APPROVED — ready for integration.
