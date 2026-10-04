# Solution Review — Conjecture 00000008837 (PR 533)

**Submission:** ziangni-sys — `ziangni-sys_submission_20261004172716`  
**Reviewer:** independent competition audit  
**Date:** 2026-10-04

## Checklist

- [x] Only the permitted submission directory was added
- [x] Full LaTeX source and PDF read; independent PDF build passed
- [x] Full Lean 4.19/Mathlib c44e project independently built
- [x] Direct warning-as-error Lean check passed
- [x] No `sorry`, `admit`, `native_decide`, custom axiom, unsafe implementation, external binding, or kernel bypass
- [x] Axiom audit shows only `propext`, `Classical.choice`, and `Quot.sound`
- [x] Probability space, filtration, martingale differences, proximal iteration, and almost-sure event match the official claim

## Counterexample

On \(\mathbb R\), define the maximal monotone graph

\[
A(x)=\{1\}.
\]

Its unit resolvent is uniquely

\[
J_A(x)=x-1,
\]

although \(A\) has no zero. On the one-point probability space with trivial filtration, take martingale-difference noise \(\xi_n=0\). Both pointwise and expected squared-noise sums are zero, so the stated square-summability condition holds.

The stochastic backward iteration

\[
X_{n+1}=J_A(X_n)+\xi_n,\qquad X_0=x,
\]

is adapted and equals

\[
X_n(\omega)=x-n.
\]

No sample trajectory converges, because consecutive differences are constantly \(-1\). Hence the convergence event is empty and has probability 0. Square-summable martingale-difference noise therefore does not guarantee almost-sure convergence for this genuine stochastic splitting iteration.

## Formal verification

Lean proves that \(A\) is maximal monotone, its resolvent equation and Lipschitz representative, exact/inexact proximal inclusions, the actual Dirac probability measure and Mathlib filtration, adaptedness/integrability/conditional expectations, both forms of square summability, trajectory recurrence, expected trajectory, emptiness of the convergence event, and failure of almost-sure convergence.

Independent `lake build` and direct warning-as-error Lean checks passed. All principal theorem audits use only the three allowed standard axioms.

## Verdict

APPROVED — correct, non-vacuous disproof of the unconditional almost-sure clause in Conjecture 00000008837.
