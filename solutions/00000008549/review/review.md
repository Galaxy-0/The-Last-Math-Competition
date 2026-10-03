# Solution Review — Conjecture 00000008549 (PR 341)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261003130000`
**Reviewer:** competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-03

## Checklist results
- Conjecture read: yes — (a) the length of maximal chains in a graded lattice is constant (definitional/true; EN "graded" vs CN "有序" slightly divergent); and (b) "the minimal example of a partition lattice with variable length is the diamond lattice"; submission refutes (b) by showing Π_3 ≅ M_3 has ALL maximal chains of length exactly 2.
- LaTeX: compiled ok (pdflatex twice, exit 0, zero errors); shipped main.pdf a real 2-page PDF (41 KB) matching main.tex; recompile also 2 pages.
- Lean build: fresh build exit 0, "Build completed successfully", `-DwarningAsError=true`; only `#print axioms` info.
- Forbidden content: none found.
- Auxiliary code: verify.cjs exit 0; identical to recorded outputs except the by-design `checkedAt` timestamp. It independently enumerates all 512 relations (exactly 5 equivalence relations: 273,283,341,433,511), re-derives partitions as blocks, checks refinement order against the diamond, and finds maximal-chain codes [19,21,25] all of length 2. My own independent python brute force over set partitions of {0,1,2} confirms: 5 partitions, diamond refinement order, maximal chains [0,a,1],[0,b,1],[0,c,1], all of length 2.
## Semantic audit
Clause (b) asserts the diamond IS a minimal partition lattice with variable maximal-chain length; that entails the diamond is a partition lattice with variable-length maximal chains. The submission proves the diamond IS a partition lattice (Π_3) but has constant maximal-chain length 2 — directly negating the entailment, hence refuting the conjunct and the stated conjunction.

Lean faithfulness: partitions are same-block equivalence relations on Fin 3, encoded as 9-bit relation codes; `every_relation_encoded`/`every_prop_partition_encoded` show ALL relations (including arbitrary Prop-valued equivalence relations) are covered, and `all_equivalence_codes` proves exactly 5 codes are equivalence relations (decide over all 512) — the genuine Π_3, matching my independent enumeration. `Refines p q := relation p ⊆ relation q` is the standard refinement order; `arbitrary_partition_refinement` proves it coincides with the diamond order for arbitrary partitions (not just the listed five). `diamond_lattice_laws` verifies the bounded lattice axioms. Chains/maximality are expressed over arbitrary proposition-valued families `MaximalPartitionChain (c : Partition → Prop)` (chain + maximal under inclusion), with encoding (`every_partition_family_encoded`, `codes_unique`) and transfer theorems (`chain_of_codes`, `maximal_chain_of_codes`, `maximal_lift`) in both directions; `all_maximal_chains` classifies the codes (only 19,21,25) and `maximal_chain_cardinality` gives cardinality 3 for each, so `every_maximal_partition_chain_length_two` and `maximal_partition_chain_length_unique : n = 2` hold for arbitrary maximal chains. `three_actual_maximal_chains` guarantees non-vacuity. Length convention: cardinality minus one (covering edges), stated in the report.

Final theorem: `conjecture_8549_diamond_claim_false : ¬ VariableMaximalChainLengths` where `VariableMaximalChainLengths := ∃ c d m n, maximal chains c,d with lengths m ≠ n` — exactly "the diamond has variable maximal-chain length". Clause (a) is deliberately untouched (it is true under the standard definition of graded, and its EN/CN wording is inconsistent); refuting one conjunct suffices. Report's chain list 0<a<1, 0<b<1, 0<c<1 matches Lean's codes 19,21,25 and my brute force.
## Issues found
- Ambiguity (non-blocking): a strained vacuous-conditional reading of clause (b) ("if any partition lattice has variable length, the smallest is the diamond") would be vacuously true since no Π_n has variable-length maximal chains; the natural assertive reading ("the diamond is such a minimal example") is what is refuted, and the submission's scope note is honest about attacking only clause (b).
## Verdict rationale
The conjecture explicitly designates the diamond as a variable-length partition-lattice example; the Lean project, working with genuine partitions as equivalence relations under the standard refinement order and quantifying over arbitrary maximal chains, proves every maximal chain of Π_3 ≅ M_3 has length 2 — so the asserted example does not exist. All builds and checks pass fresh, and my independent brute force agrees. Genuine disproof of the statement as written.

## Disposition
APPROVED — merged into main (PR 341). Independent fresh rebuild of the Lean project (Lean 4.19.0, `lake build` with warnings-as-errors, exit 0, axioms limited to the standard Lean foundational set), LaTeX recompilation, auxiliary-script re-runs, and a semantic audit confirming the Lean theorem refutes the conjecture as stated in both language versions.
