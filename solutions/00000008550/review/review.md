# Solution Review — Conjecture 00000008550 (PR 397)

**Submission:** ziangni-sys — `ziangni-sys_submission_20261004041645`
**Reviewer:** competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-04

## Checklist results
- Conjecture read: yes — "Kernel ideals correspond one-to-one with congruences; and the maximal chain length of a kernel is the tower height of the lattice, decreasing under passage to sublattices" (disproof submission).
- LaTeX: pdflatex twice, exit 0 both passes, 0 errors; shipped report.pdf is a genuine 2-page PDF matching report.tex content.
- Lean build: `lake build` exit 0, "Build completed successfully", no warnings; six `#print axioms` lines — standard logical axioms only (quotient_homomorphisms on [propext] alone, the rest on [propext, Classical.choice, Quot.sound]).
- Forbidden content: grep over lean/Main.lean, lakefile.lean, verify.py — no hits (no sorry/admit/native_decide/axiom decls/unsafe/implemented_by/extern/skipKernelTC; set_option uses are only maxHeartbeats/maxRecDepth, which are performance options, not kernel bypasses).
- Auxiliary code: `python3 verify.py` exit 0; its output matches verification/python-check.txt EXACTLY (all 4 lines). verification/source.md is byte-identical (diff) to the official conjecture. Hand re-derivation: the 5 partitions of {0,1,2} — all except {{0,2},{1}} (0~2 would force 0~1 via min with 1) are congruences ⇒ exactly 4 congruences; ideals containing 0, downward and join closed are exactly {0}, {0,1}, C_3 ⇒ 3; kernel of identity congruence and of the {1,2}-identifying congruence are both {0}. All confirmed by both the Python check and the Lean decide proofs.
## Semantic audit
Conjecture literal claim (EN): "Kernel ideals correspond one-to-one with congruences." (CN: 核理想与同余一一对应.) The submission refutes the first conjunct on the 3-element bounded chain C_3 = {0<1<2}; the tower-height clause is untouched (unnecessary — the conjunction is falsified).

Lean encodings (namespace `KernelIdealCounterexample`, ambient `abbrev Chain := Fin 3` with Mathlib's actual BoundedOrder/Lattice instances; min/max = the chain's meet/join):
- `def IsCongruence (r : Relation) : Prop` — full equivalence (reflexivity, symmetry, transitivity) plus two-argument compatibility with BOTH min and max: the standard lattice-congruence definition.
- `def BoundedHom {n} (q : Chain → Fin (n+1)) : Prop` — preserves min, max, bottom, top; the four quotients (identity, upper {1,2}-identifying, lower {0,1}-identifying, trivial) are proved genuine bounded-lattice surjections (`quotient_homomorphisms`, `quotient_surjections`, kernel-checked decide).
- `def kernel (r : Relation) : Finset Chain := Finset.univ.filter (fun x => r 0 x = true)` — the kernel ideal as the actual zero class, with `quotient_zero_classes` proving agreement with the quotient's zero preimage.
- `def IsIdeal (K : Finset Chain) : Prop := 0 ∈ K ∧ (downward closed) ∧ (join closed)` — standard lattice ideal.
- Exhaustive classification: `congruences_classified` checks all 2^9 = 512 Boolean relations; `congruence_count : congruences.card = 4`, `ideal_count : ideals.card = 3`, `every_ideal_is_kernel : kernelIdeals = ideals`, `kernel_ideal_count : kernelIdeals.card = 3`, `all_ideals_realized`.

Decisive theorems:
- `theorem distinct_same_kernel : equalityRelation ≠ upperRelation ∧ kernel equalityRelation = kernel upperRelation ∧ kernel equalityRelation = {0} ∧ IsIdeal (kernel equalityRelation)` — two distinct congruences with the same kernel ideal: the natural correspondence is not injective (`natural_correspondence_not_injective : ¬ Function.Injective kernel`).
- `theorem conjecture_00000008550_correspondence_false : ¬ Nonempty (↥congruences ≃ ↥kernelIdeals)` — by Fintype.card_congr, 4 ≠ 3, so even an ABSTRACT bijection reading is refuted. The count uses `kernelIdeals := congruences.image kernel` (the actual kernel-ideal set), so the conclusion is independent of the all-ideals convention (counting ∅ as an ideal would not change kernelIdeals = 3, and non-injectivity is proved directly).

Non-vacuousness: the lattice is a genuine bounded lattice, the quotients are genuine bounded-lattice surjections, all three ideals are realized as actual kernels (no missing candidate is suppressed), and the classification is exhaustive over all 512 relations. This is the standard, correct mathematics: unlike rings, lattice congruences are not determined by their zero classes, and C_3 is the minimal witness. The README transparently notes C_3 also appears in a separate submission (08557) addressing a different source claim.
## Issues found
none blocking
## Verdict rationale
The Lean project builds cleanly with only standard axioms, exhaustively classifies congruences and kernel ideals of C_3 by kernel-checked decision procedures (not assumed lists), and proves both that the natural kernel map is non-injective and that no abstract bijection exists (4 congruences vs 3 kernel ideals). The Python auxiliary check runs, exits 0, and reproduces its recorded output exactly; the mathematical content was independently re-verified by hand. Report, PDF, and verification evidence are all consistent. Approved.

## Disposition
APPROVED — merged into main (PR 397). Independent fresh rebuild of the Lean project (Mathlib-pinned, exit 0; only standard foundational axioms; no sorry/native_decide/extra axioms), LaTeX recompilation, auxiliary-script re-runs where shipped, independent recomputations, and a semantic audit confirming the Lean theorem establishes or refutes the conjecture as stated in both language versions.
