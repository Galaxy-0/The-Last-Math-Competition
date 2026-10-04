# Solution Review — Conjecture 00000009626 (PR 445)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261004105732`  
**Reviewer:** independent competition audit  
**Date:** 2026-10-04

## Checklist

- [x] Only the permitted submission directory was added
- [x] Full LaTeX source and PDF read; independent LaTeX build passed
- [x] Lean 4.19/Mathlib c44e project independently built from exact pins
- [x] Direct warning-as-error Lean check passed
- [x] Auxiliary Python enumeration run independently
- [x] No `sorry`, `admit`, `native_decide`, custom axiom, unsafe implementation, external binding, or kernel bypass
- [x] Axiom audit shows only allowed standard axioms

## Counterexample

The official statement does not restrict two-dimensional SFTs to a binary alphabet. The full shift on three symbols,

\[
X=\{0,1,2\}^{\mathbb Z^2},
\]

is a two-dimensional SFT with no forbidden patterns. Every pattern on an \(n\times n\) square occurs independently, so

\[
N_X(n)=3^{n^2}
\]

and

\[
h(X)=\lim_{n\to\infty}\frac{\log 3^{n^2}}{n^2}=\log3.
\]

Since \(\log3>\log2\), this genuine SFT entropy lies outside the claimed spectrum \([0,\log2]\). Therefore the realizable entropy values cannot constitute that interval.

The scope is explicit: this disproves the unrestricted submitted statement, not a modified conjecture imposing a binary alphabet.

## Formal verification

Lean defines actual \(\mathbb Z^2\) configurations over `Fin 3`, forbidden-pattern SFT presentations, global pattern occurrence, exact finite subtype cardinalities, real logarithmic normalized counts, and convergence at infinity. It proves the empty-forbidden-set full shift is an SFT, every pattern extends, \(N(n)=3^{n^2}\), entropy equals \(\log3\), and the universal \(\log2\) bound fails.

Independent `lake build` and direct warning-as-error Lean compilation passed. The supplemental Python enumeration also passed. Principal theorem audits use only `propext`, `Classical.choice`, and `Quot.sound`.

## Verdict

APPROVED — correct, non-vacuous disproof of Conjecture 00000009626.
