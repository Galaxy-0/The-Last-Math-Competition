# Solution Review — Conjecture 00000004274 (PR 310)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261003091740`
**Reviewer:** competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-03

## Checklist results
- Conjecture read: yes — For a countable p-group, the center of Aut(G) is nontrivial iff a characteristic element exists, and the count of central elements is read off the Ulm sequence as a termwise product of powers of 2.
- LaTeX: compiled ok (pdflatex run twice, exit 0 both), 1-page PDF produced; included main.pdf is a genuine PDF (43 KB, v1.5), page count matches verification.json (1 page).
- Lean build: fresh `rm -rf .lake && lake build` exit 0, zero warnings (warnings-as-errors enabled via `-DwarningAsError=true`), toolchain v4.19.0.
- Forbidden content: none — grep for sorry/admit/native_decide/axiom/unsafe/implemented_by/extern over Main.lean found nothing.
- Auxiliary code: none present (`auxiliary_scripts_rerun: []` in verification.json); sha256 of lean/Main.lean and main.tex match verification.json records exactly; reproduced axiom printout (propext, Quot.sound only) matches lean-verification.txt.
## Semantic audit
Conjecture's literal claim (EN): "the count of central elements is read off explicitly from the Ulm sequence, and the formula is a termwise product of powers of 2" for countable p-groups, where the center of Aut(G) is defined as elements commuting with all automorphisms.

Lean encodings verified faithful:
- `abbrev C7 := Fin 7`; `Additive/Injective/Surjective` are real function properties; `Aut := {f : C7 → C7 // Additive f ∧ Injective f ∧ Surjective f}` — automorphisms are actual functions, not an abstract index.
- Hypotheses checked in Lean: `seven_prime` (7 prime), `seven_annihilates : ∀ a, multiples a 7 = 0` (p-group), `carrier_countable` (injection to Nat), `cyclic_group_laws` (abelian group axioms). So C7 is a countable p-group as the conjecture requires.
- `Central (a : Aut) : Prop := ∀ b : Aut, ∀ x, a.val (b.val x) = b.val (a.val x)` — exactly "commutes with every automorphism"; `Center := {a : Aut // Central a}`.
- Structural bridge proved, not assumed: `generated_by_one` (every endomorphism is multiplication by f 1, by symbolic induction on multiples), `aut_reconstruction`/`unit_roundtrip` (Aut ≅ Fin 6 via unitIndex/autOfUnit), `all_automorphisms_central`, `center_has_six_elements : Bijection Center (Fin 6)`, `centerEnumeration_complete` (every central element in list), `centerEnumeration_nodup`, `centerEnumeration_cardinality : length = 6`.
- Final theorems: `powerProduct_is_power : powerProduct es = 2^es.sum` (a termwise product of powers of 2 is a power of 2); `six_not_power_of_two : ∀ n : Nat, 6 ≠ 2^n`; `conjecture04274_false : ¬ ClaimedCenterPowerProduct` where `ClaimedCenterPowerProduct` says every complete duplicate-free enumeration of the actual Center has length a powerProduct; and `full_conjecture_false (OtherAssertions) : ¬ (OtherAssertions ∧ ClaimedCenterPowerProduct)` covering the conjunctive form.
- Logical contradiction: conjecture predicts |Z(Aut(C7))| is a termwise product of powers of 2 (hence 2^k); Lean proves the actual center has exactly 6 elements and 6 ≠ 2^k for all k. Genuine contradiction; not vacuous — the decisive objects (group, automorphisms as functions, center, complete enumeration) are all present, unlike the rejected PRs #286–288 pattern.
- LaTeX↔Lean match: report states Aut(G) = {m_a : a ∈ 1..6}, |Z(Aut)| = 6, 6 not a power of 2, inverse multipliers 1,4,5,2,3,6 — identical to Lean's `inverseUnit` table and theorem statements.
- Report's robustness note is correct: C7 has only one nonzero Ulm invariant u_0 = 1, so trailing-zero factors are 1 and the product stays a power of 2 under any finite-or-countable reading.
## Issues found
- Minor (non-blocking): the submission refutes the counting clause, not the "iff characteristic element exists" clause; that is sufficient since the conjecture is conjunctive, and `full_conjecture_false` makes this explicit.
- Interpretation note (non-blocking, documented in SOURCE.md/report): exponents read as nonnegative integers/finite cardinals; under real exponents the clause would be vacuous, but the counting reading is the only mathematically meaningful one.
## Verdict rationale
The Lean development constructs the actual automorphism group of C7 as functions, proves a complete duplicate-free enumeration of its center has 6 elements, and proves 6 is not a power of 2, directly contradicting the conjecture's power-of-two counting formula for a genuine countable p-group. Fresh build passes with warnings-as-errors and only standard axioms; the LaTeX compiles and matches the Lean content. This is a genuine disproof of the conjecture as stated.

## Disposition
APPROVED — merged into main (PR 310). Independent fresh rebuild of the Lean project (Lean 4.19.0, `lake build` with warnings-as-errors, exit 0, axioms limited to the standard Lean foundational set), LaTeX recompilation, auxiliary-script re-runs, and a semantic audit confirming the Lean theorem refutes the conjecture as stated in both language versions.
