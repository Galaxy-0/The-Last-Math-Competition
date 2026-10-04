# Solution Review — Conjecture 00000009650 (PR 446)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261004110741`  
**Reviewer:** independent competition audit  
**Date:** 2026-10-04

## Checklist

- [x] Only the permitted submission directory was added
- [x] Full LaTeX source and PDF read; independent PDF build passed
- [x] Lean 4.19/Mathlib c44e exact-pin project independently built
- [x] Direct warning-as-error Lean check passed
- [x] Auxiliary exact-rational Python program independently run
- [x] No `sorry`, `admit`, `native_decide`, custom axiom, unsafe implementation, external binding, or kernel bypass
- [x] Principal axiom audit shows only `propext`, `Classical.choice`, and `Quot.sound`

## Counterexample

The official overlap is the squared inner product of eigenvectors belonging to distinct eigenvalues of the same matrix. For any real symmetric \(T\),

\[
Tu_i=\lambda_i u_i,\quad Tu_j=\lambda_j u_j,\quad \lambda_i\ne\lambda_j
\]

implies

\[
\lambda_i\langle u_i,u_j\rangle
=\langle Tu_i,u_j\rangle
=\langle u_i,Tu_j\rangle
=\lambda_j\langle u_i,u_j\rangle,
\]

so \(\langle u_i,u_j\rangle=0\) and \(o_{ij}=0\). Thus every strict-upper overlap is zero; the empirical law is \(\delta_0\), not a measure with the claimed density. Its mean is exactly \(0\), not \(2/n\), and \(n\) times the mean remains identically \(0\), not asymptotic to \(2\).

This applies to the real symmetric/GOE class, so the claimed universality cannot hold. The submission clearly limits its conclusion to the literal same-matrix overlap and does not claim a result for a different independent-matrix or non-Hermitian statistic.

## Formal verification

Lean proves orthogonality from actual self-adjointness and distinct eigenvalues, defines the strict-upper pair set and empirical test-function average, and proves the point-mass identity. It proves exact and scaled mean contradictions for any real symmetric simple-spectrum eigensystem and supplies concrete normalized diagonal eigensystems in every dimension.

Independent `lake build`, direct warning-as-error Lean, LaTeX, and exact Python checks all passed. Principal theorem audits use only the three allowed standard axioms.

## Verdict

APPROVED — correct, non-vacuous disproof of the literal Conjecture 00000009650.
