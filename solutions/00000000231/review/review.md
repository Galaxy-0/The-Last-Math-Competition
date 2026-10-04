# Solution Review — Conjecture 00000000231 (PR 442)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261004102602`  
**Reviewer:** independent competition audit  
**Date:** 2026-10-04

## Checklist

- [x] Only the permitted submission directory was added
- [x] Full LaTeX source and PDF read; independent PDF build passed
- [x] Self-contained Lean project independently built
- [x] Direct warning-as-error Lean check passed
- [x] Auxiliary Python program run and its exact outputs independently reproduced
- [x] No `sorry`, `admit`, `native_decide`, custom axiom, unsafe implementation, external binding, or kernel bypass
- [x] Axiom audit shows only `propext` and `Quot.sound`

## Literal counterexample

Following the official bilingual definition, an exceptional prime is one whose Fibonacci period does not divide \(p^2\). For \(p=7\):

\[
\pi(7)=16,\qquad \pi(49)=112.
\]

Neither period divides

\[
p^2=49,
\]

and \(7<10^{17}\) is prime. Thus 7 is a counterexample whether “Fibonacci period” is read modulo \(p\) or modulo \(p^2\). The universal assertion that no such prime exists below \(10^{17}\) is therefore false.

The submission correctly distinguishes this literal condition from the conventional Wall–Sun–Sun condition \(\pi(p^2)=\pi(p)\). Since \(112\ne16\), it does not claim 7 is conventional; it only disproves the official statement as written.

## Verification

Lean defines the genuine Fibonacci recurrence on all naturals, proves uniqueness, defines a period by congruence at every index, and proves that a first return of the residue pair \((F_n,F_{n+1})\) with no smaller return certifies the least period of the entire sequence. Kernel-checked finite certificates establish periods 16 and 112, primality, nondivisibility, and the bound.

Independent `lake build`, direct warning-as-error Lean, LaTeX compilation, and `python verify.py` all exited 0. The script’s exact residue-orbit outputs were also reproduced independently. Principal Lean declarations depend only on `propext` and `Quot.sound`.

## Verdict

APPROVED — correct, non-vacuous disproof of the literal Conjecture 00000000231.
