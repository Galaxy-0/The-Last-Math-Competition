# Solution Review — Conjecture 00000001000 (PR 383)

**Submission:** ziangni-sys — `ziangni-sys_submission_20261004031634`
**Reviewer:** competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-04

## Checklist results
- Conjecture read: yes — "The smallest Tarski number is 6, realized by a finite quotient of the Burnside group B(m,n) at (m,n) = (2,5); every group of Tarski number 6 is of Burnside type, with no other mechanism" (EN+CN agree; Tarski number = number of pieces in a paradoxical decomposition).
- LaTeX: recompiled in /tmp/tlmc-review5/scratch/pr-383 with pdflatex twice, exit 0, zero errors; shipped report.pdf is a genuine PDF (37,319 bytes, tectonic/CID) whose title and digit runs match report.tex ("A finite group cannot realize a Tarski number", conjecture ID); full report read — standard paradoxical-decomposition definition, the |G| = 2|G| counting proof, the tagged-map G → G ⊕ G formulation, and why it covers every finite quotient of B(2,5).
- Lean build: `lake build` exit 0 ("Build completed successfully", 2794 targets — identical to the submitter's lean-build.txt; the environment's pruned cache lacked ~1000 oleans of the `Mathlib.Tactic` closure, which were compiled from source). Zero warnings. `#print axioms`: translated_surjective/injective → [propext]; no_finite_paradoxical_decomposition / conjecture_00000001000_false → [propext, Classical.choice, Quot.sound].
- Forbidden content: grep for `sorry`, `admit`, `native_decide`, `axiom `, `unsafe`, `implemented_by`, `extern`, `skipKernelTC` over Main.lean — no matches; no custom axioms.
- Auxiliary code: none shipped, none needed (universal counting proof); my own independent checks: 2k ≤ k impossible for all k ≥ 1, and exhaustive searches found no configuration satisfying even the cover field of a paradoxical decomposition on Z/2 with n = 6 pieces (all 262,144 label/side/multiplier combinations), nor on Z/3 (n = 3, 4) nor Z/4 (n = 2) — consistent with the Lean theorem.
## Semantic audit
Conjecture literal claim (first conjunct): the smallest Tarski number is 6, realized by a finite quotient of B(2,5). A group realizes Tarski number 6 only if it admits a paradoxical decomposition with 6 pieces; the conjecture's own definition fixes "Tarski number = number of pieces in a paradoxical decomposition". A finite quotient is a finite (nonempty) group. The submission proves no finite group admits a paradoxical decomposition with any number of pieces, hence no finite quotient of B(2,5) realizes Tarski number 6 — refuting the asserted witness and thereby the conjunction. (The conjecture is in fact doubly false: F₂ has Tarski number 4 < 6; the submission does not rely on this.)

Lean encoding of the conjecture's object:

```lean
structure ParadoxicalDecomposition (G : Type*) [Group G] (n : Nat) where
  label : G → Fin n
  side : Fin n → Bool
  multiplier : Fin n → G
  covers : ∀ b : Bool, ∀ y : G, ∃ x : G, side (label x) = b ∧ multiplier (label x) * x = y
  separates : ∀ x z : G, side (label x) = side (label z) →
    multiplier (label x) * x = multiplier (label z) * z → x = z
```

(i) Faithfulness: the label fibers are exactly the pieces (they partition G — `partition_covers`, `partition_disjoint`); `covers` says the left-translated pieces of each side separately reassemble all of G (G = ⊔ a_i A_i = ⊔ b_j B_j with genuine left multiplication `multiplier (label x) * x`); `separates` says translated images within a side are disjoint. This is the standard paradoxical decomposition with n labeled pieces (empty pieces allowed, which only weakens the hypotheses of the refuted statement — the submission notes this and it is the conservative direction for a disproof). (ii) Main results: `translated_surjective` and `translated_injective` for the tagged map x ↦ (side, multiplier·x) : G → G ⊕ G, and

```lean
theorem no_finite_paradoxical_decomposition [Fintype G] (n : Nat) : ¬ Nonempty (ParadoxicalDecomposition G n)
theorem conjecture_00000001000_false (Q : Type*) [Group Q] [Fintype Q] : ¬ HasSixPieceParadox Q
```

derived via `Fintype.card_le_of_surjective` giving 2·|G| ≤ |G| with 0 < |G| — the classical amenability-of-finite-groups counting argument, complete and independent of the number of pieces. (iii) The final theorem contradicts the conjecture's realization clause: any finite quotient Q of B(2,5) is a `Group Q` with `Fintype Q`, so it cannot carry a 6-piece paradoxical decomposition and cannot have Tarski number 6. The step "finite quotient ⇒ finite group" is trivial and stated in the report; Lean quantifies over all finite groups, which is strictly stronger than needed. (iv) Not vacuous: hypotheses are exactly [Group Q] [Fintype Q] ("finite group"); the theorem has real content (excludes all finite quotients of any group, Burnside or not). Not a numeric-facts-only proof: the obstruction is proved universally.
## Issues found
- Note (non-blocking): the Lean final theorem is stated for all finite groups rather than literally mentioning quotients of B(2,5); the bridge (a finite quotient is a finite group) is immediate and fully explained in the report — the universal form is strictly stronger than the quotient-specific statement.
- Note (non-blocking): the submission refutes the realization clause and explicitly does not address the "smallest Tarski number" or classification clauses; since the conjecture is a conjunction asserting the finite-quotient witness, refuting one conjunct is a valid disproof under the literal-statement-is-authoritative precedent. (Independently, the "smallest is 6" clause is also false — F₂ has Tarski number 4 — so the conjecture is false on any reading.)
- Minor (non-blocking): README "Reproduce" mentions `lake exe cache get`; unnecessary with the pinned manifest.
## Verdict rationale
The submission gives a complete, formalized proof of the classical fact that no finite group admits a paradoxical decomposition (2|G| ≤ |G| with |G| ≥ 1 is contradictory), with a structure that faithfully encodes the conjecture's own definition of paradoxical decomposition and Tarski number. This directly refutes the conjecture's literal assertion that a finite quotient of B(2,5) realizes Tarski number 6, since a finite quotient is a finite group. The build is clean with only standard axioms, the report compiles and matches the shipped PDF, and my independent exhaustive searches confirm the obstruction.

## Disposition
APPROVED — merged into main (PR 383). Independent fresh rebuild of the Lean project (exit 0; only standard foundational axioms; no sorry/native_decide/extra axioms), LaTeX recompilation, auxiliary-script re-runs where shipped, independent recomputations, and a semantic audit confirming the Lean theorem establishes or refutes the conjecture as stated in both language versions.
