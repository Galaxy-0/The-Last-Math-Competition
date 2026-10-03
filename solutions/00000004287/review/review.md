# Solution Review — Conjecture 00000004287 (PR 335)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261003104000`
**Reviewer:** competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-03

## Checklist results
- Conjecture read: yes — "the length threshold for unions of chains of pure subgroups to remain pure is exactly omega, every chain length beyond omega has an explicit counterexample, and the rank of the counterexample equals the chain length," with pure defined as torsion-free quotient.
- LaTeX: compiled ok (pdflatex x2, exit 0, 0 errors, 2 pages); shipped main.pdf is a real PDF v1.5, 2 pages, 38 KB, hash matches verification.json.
- Lean build: fresh `rm -rf .lake && lake build` exit 0, "Build completed successfully", warnings-as-errors enabled; toolchain v4.19.0; no warnings.
- Forbidden content: none — no `sorry`, `admit` (word or tactic), `native_decide`, `axiom`, `unsafe`, `@[implemented_by]`, `extern`. All listed theorems depend only on [propext, Quot.sound].
- Auxiliary code: none shipped (deductive proof, nothing computational claimed); verification.json records auxiliary_scripts_rerun: []. All recorded SHA256 hashes match the on-disk files.
- Folder name: `gaochengzhecpu_submission_20261003104000` — matches the pattern.
## Semantic audit
Conjecture's decisive claims: (a) a length threshold at ω for closure of purity under chain unions, (b) existence of explicit counterexamples at EVERY chain length beyond ω. The submission proves the universal positive statement, which kills (b) and hence the "threshold exactly ω" assertion (a). Key Lean definitions, all faithful:
- `GroupData A` = a group (assoc, unit, both inverse laws) in additive notation; `Subgroup D` = Prop-valued carrier closed under 0, +, −, plus normality (exactly what is needed for a quotient group; automatic in the abelian setting the conjecture lives in).
- `Pure H := TorsionFree (quotientStructure H)` — the quotient is an ACTUAL Lean `Quotient` of the coset relation `∃ h ∈ H, x + h = y` with equivalence, compatibility with + and − (proved via normality), and every group law in `quotientStructure`; `TorsionFree` = ∀ n > 0, n·x = 0 → x = 0. This is literally the conjecture's definition ("quotient under inclusion is torsion-free"), not a substitute; `pure_iff_rootClosed` derives the nx ∈ H ⇒ x ∈ H criterion as a theorem.
- `Chain H := ∀ i j, Included (H i) (H j) ∨ Included (H j) (H i)` — a chain of subgroups indexed by an ARBITRARY type, so every ordinal-indexed chain (any length) is covered after forgetting the length, as the report explains.
Final theorems:
- `directed_union_pure : ∀ H, Nonempty I → Directed H → (∀ i, Pure (H i)) → Pure (unionSubgroup H hI hd)` (union constructed as a real normal subgroup)
- `arbitrary_chain_union_pure` (chains are directed)
- `conjecture04287_false : ¬ ClaimedFailureExists` where `ClaimedFailureExists := ∃ (A : Type) (D : GroupData A), BadChainExists D` and `BadChainExists D := ∃ (I : Type) (H : I → Subgroup D) (hI : Nonempty I) (hc : Chain H), (∀ i, Pure (H i)) ∧ ¬ Pure (unionSubgroup ...)`.
The mathematics is standard and correct: if n·x ∈ ⋃ H_i then n·x ∈ H_i for some i, root-closedness of H_i gives x ∈ H_i ⊆ ⋃; hence every nonempty directed (in particular chain) union of pure subgroups is pure, for groups of any size, so no counterexample chain can exist at any length, beyond ω or otherwise. This directly contradicts clause (b) of the conjecture ("every chain length beyond omega has an explicit counterexample") and shows closure holds at all lengths (so no ω threshold exists). The proof engages the conjecture's actual objects (real quotient groups, real torsion-freeness, real chains and unions) and is not vacuous — it is a universal theorem refuting the conjecture's existence claim; the "rank equals chain length" clause concerns the nonexistent counterexamples.
## Issues found
none blocking
## Verdict rationale
The Lean project builds fresh with warnings-as-errors and only standard axioms, the LaTeX compiles to the matching 2-page PDF, and the formalization constructs the actual quotient group and proves the universal chain-union closure theorem using precisely the conjecture's definition of purity. The conjecture's assertion that counterexamples exist at every chain length beyond ω is therefore refuted outright — there are none at any length — which is a genuine, non-vacuous disproof of the conjecture as stated in both languages.

## Disposition
APPROVED — merged into main (PR 335). Independent fresh rebuild of the Lean project (Lean 4.19.0, `lake build` with warnings-as-errors, exit 0, axioms limited to the standard Lean foundational set), LaTeX recompilation, auxiliary-script re-runs, and a semantic audit confirming the Lean theorem refutes the conjecture as stated in both language versions.
