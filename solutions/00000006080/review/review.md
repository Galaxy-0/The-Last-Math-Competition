# Solution Review — Conjecture 00000006080 (PR 513)

**Submission:** ziangni-sys — `ziangni-sys_submission_20261004162922`  
**Reviewer:** independent competition audit  
**Date:** 2026-10-04

## Checklist

- [x] Only the permitted submission directory was added
- [x] Full LaTeX source and PDF read; independent PDF build passed
- [x] Full pinned Lean project independently built
- [x] Direct Lean compilation and axiom audit passed
- [x] No `sorry`, `admit`, `native_decide`, custom axiom, unsafe implementation, external binding, or kernel bypass
- [x] Principal axioms are only `propext`, `Classical.choice`, and `Quot.sound`
- [x] Formal networks, minima, saddle Hessians, spectra, and perturbation match the conjecture

## Construction

The submission uses explicit square-activation feedforward networks whose outputs are

\[
L_1(x,y)=(x^2-1)^2+y^2,\qquad
L_2(x,y)=2(x^2-1)^2+y^2.
\]

For every \(c>0\), \(L_c\ge0\), with equality exactly at \((-1,0)\) and \((1,0)\). Hence both networks have exactly the same local/global minimum positions and value 0.

The derivative is zero only at \((-1,0),(0,0),(1,0)\). The origin is not a minimum because nearby points \((t,0)\) lower the loss. Its Hessian is

\[
\begin{pmatrix}-4c&0\\0&2\end{pmatrix},
\]

so it is a strict saddle with full spectrum \(\{-4c,2\}\). Therefore the two saddle spectra are

\[
\{-4,2\}\ne\{-8,2\}.
\]

Changing the first output weight from 1 to 2 gives the explicit perturbation

\[
L_2-L_1=(x^2-1)^2,
\]

which preserves all minima and changes the saddle spectrum.

## Formal verification

Lean defines actual affine layers, square activations, network evaluation, and output weights, then derives the polynomial formula rather than assuming it. It proves Fréchet differentiability, complete local/global minimum sets, minimum values, actual second-partial Hessians, full Mathlib spectra, strict-saddle behavior, spectrum inequality, and the explicit perturbation in one existential theorem.

Independent `lake build` and direct Lean compilation passed; all twelve principal theorem audits use only the three allowed standard axioms. A warning-as-error run reports only repeated style-linter `unnecessarySeqFocus` diagnostics, not incomplete or unsound proofs.

## Verdict

APPROVED — this proves Conjecture 00000006080 with explicit, non-vacuous networks.
