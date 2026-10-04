# Solution Review — Conjecture 00000000036 (PR 444)

**Submission:** champagnepapihz — `champagnepapihz_submission_20261004120000`  
**Reviewer:** independent competition audit  
**Date:** 2026-10-04

## Checklist

- [x] Only the permitted submission directory was added
- [x] Full LaTeX source and PDF read; independent LaTeX build passed
- [x] Pinned Lean 4.33/Mathlib v4.33 project independently built
- [x] Entry-point warning-as-error Lean check and independent axiom audit passed
- [x] No `sorry`, `admit`, `native_decide`, custom axiom, unsafe implementation, external binding, or kernel bypass
- [x] Axioms are only the allowed `propext`, `Classical.choice`, and `Quot.sound`

## Counterexample to the claimed construction

The conjecture says that the residue classes \(\{\pm1\bmod6\}\) give the claimed admissible density \(1/3\). They do not: both

\[
5\equiv -1 \pmod 6,\qquad 7\equiv 1\pmod 6
\]

belong to the proposed set, but

\[
7-5=2\ge2
\]

is prime. Thus the proposed extremal set violates the conjecture’s composite-difference hypothesis and cannot attain the asserted \(1/3\) construction. The official statement is therefore false as stated.

## Corrected construction

The positive multiples of 4 are admissible. Distinct members have an even sum at least 12 and an even positive difference at least 4, so both are composite. Their count in \([1,N]\) is \(\lfloor N/4\rfloor\), giving density \(1/4\). Lean proves both admissibility implications and this explicit counting inequality.

## Verification

The complete project built successfully under the pinned Lean 4.33.1/Mathlib v4.33.1 revisions. The entry-point warning-as-error check passed. An independent import printed the decisive theorem’s axioms as exactly `propext`, `Classical.choice`, and `Quot.sound`. Only concrete witness checks use kernel `decide`; no native oracle or custom axiom appears.

## Verdict

APPROVED — correct, non-vacuous refutation of the stated extremal construction in Conjecture 00000000036.
