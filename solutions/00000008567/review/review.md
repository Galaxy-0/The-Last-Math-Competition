# Solution Review — Conjecture 00000008567 (PR 441)

**Submission:** ziangni-sys — `ziangni-sys_submission_20261004095255`  
**Reviewer:** independent competition audit  
**Date:** 2026-10-04

## Checklist

- [x] Only the permitted submission directory was added
- [x] Full LaTeX source and PDF read; independent PDF build passed
- [x] Full pinned Lean project independently built
- [x] Direct warning-as-error Lean check passed
- [x] Only standard axioms `propext`, `Classical.choice`, and `Quot.sound`
- [x] No incomplete proof, external implementation, native decision shortcut, or custom axiom
- [x] Formal row blocks, principal compressions, partitions, norms, and identity matrix correspond to the official statement

## Counterexample

The official statement is unrestricted: partition a matrix by rows so every block norm is at most \((1-\varepsilon)^2\) times the full norm. Take \(A=I_n\), \(n\ge1\), and \(\varepsilon=1/2\). Then \(\|A\|=1\), so every block would need norm at most \(1/4\).

If a block contains row coordinate \(i\), the orthogonal row restriction \(R_S=P_SI\) fixes the unit vector \(e_i\). Therefore

\[
\|R_S\|\ge \|R_S e_i\|/\|e_i\|=1.
\]

The principal compression \(\widetilde P_S I\widetilde P_S\) also fixes \(e_i\), so its norm is at least 1. Since a partition must cover the nonempty coordinate set, some block contains a coordinate, contradicting the \(1/4\) requirement. Thus no finite number \(r\) can pave this matrix, including any claimed \(O(\varepsilon^{-2}\log n)\) quantity.

This addresses the literal unrestricted statement. It does not contradict the standard zero-diagonal/off-diagonal Kadison–Singer paving theorem; the report states that scope distinction explicitly.

## Formal verification

Lean uses actual `EuclideanSpace`, its orthonormal coordinate basis, the identity continuous linear map and its identity matrix representation, coordinate spans, orthogonal projections, and continuous-linear-map operator norms. It proves the row action/norm lower bound, the analogous principal-compression bound, and impossibility for every finite disjoint covering partition in every positive dimension. The proof quantifies over all covering block families, so overlaps cannot rescue it.

Independent `lake build` and direct warning-as-error Lean compilation both passed. All seven principal audits list exactly the three standard logical axioms.

## Verdict

APPROVED — correct, non-vacuous disproof of the unrestricted Conjecture 00000008567.
