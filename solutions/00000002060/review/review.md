# Solution Review — Conjecture 00000002060 (PR 464)

**Submission:** feiyuceng06-prog — `feiyuceng06-prog_submission_20261004052337`
**Reviewer:** independent competition review (structure, build, semantics)
**Date:** 2026-10-04

## Checklist
- [x] Official bilingual conjecture read in full
- [x] LaTeX source and shipped PDF read; independent PDF builds passed
- [x] Full Lean project independently rebuilt
- [x] Direct warnings-as-errors checks passed
- [x] Only standard foundational axioms reported
- [x] No incomplete-proof or kernel-bypass constructs
- [x] No auxiliary program shipped, so no auxiliary run was omitted
- [x] Submission adds only its own correctly named folder
- [x] Conjecture unsolved in base metadata

## Conjecture and reading
The official claim says that the spectrum-derived set for finite groups consists of prime powers and squarefree orders, and explicitly states that the complement — orders which are neither prime powers nor squarefree — is not realizable. The submission takes the literal variety of groups and finite-member spectrum, and refutes this exclusion clause.

## Counterexample
The cyclic group \(C_{12}=(\mathbb Z/12\mathbb Z,+)\) is a finite group of order 12. Since
\[
12=2^2\cdot3,
\]
it is neither a prime power nor squarefree. Thus an order in the conjecture's alleged non-realizable complement is realized by an actual finite group.

## Formal audit
`FiniteGroupOrderOccurs n` asks for a genuine type with `Group` and `Fintype` instances and cardinality `n`. The witness is `Multiplicative (ZMod 12)`, representing the additive cyclic group as a multiplicative group. Lean proves its cardinality is 12, proves 12 is neither a prime power nor `Squarefree`, and negates the formal universal claim that every finite-group order is prime-power-or-squarefree.

A full fresh `lake build` succeeded (8708 jobs), as did direct warnings-as-errors elaboration. The final theorem depends only on `propext`, `Classical.choice`, and `Quot.sound`. No `sorry`, `admit`, `native_decide`, custom axiom, unsafe construct, external implementation, or kernel-check bypass occurs.

## Documentation audit
The complete two-page report was read. Independent pdfLaTeX and XeLaTeX builds both succeeded twice. The fresh XeLaTeX PDF has exactly the same normalized extracted text as the shipped PDF and accurately explains the witness, arithmetic, formal encoding, and scope limitation.

## Semantic conclusion
The witness is an actual finite group, not merely the integer 12. It lies squarely in the complement excluded by both the English and Chinese conjecture text. Therefore the stated conjecture is false.

## Verdict
APPROVED — ready for integration.
