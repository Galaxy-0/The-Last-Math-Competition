# Solution Review — Conjecture 00000008330 (PR 664)

**Submission:** Jackmeson1 — `solutions/00000008330/Jackmeson1_submission_20261005085627`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

## Checklist results

- Conjecture 00000008330 read in full (official bilingual English+Chinese text, ground truth). Shipped `conjecture.md` is **byte-identical** to `conjectures/00000008330.md` (`diff` clean).
- LaTeX: read the entire `proof.tex` (131 lines). Rebuilt independently with `latexmk -pdf -interaction=nonstopmode` in a scratch dir from the shipped source; build succeeded. Shipped vs rebuilt PDF text compared with pypdf (whitespace- then glyph-normalized): identical modulo pure extraction artifacts (title math parens mapping to control glyphs, `∩`/`T` big-operator glyph, math-boundary spacing), same normalized length 3876 chars.
- Lean: `lake build` succeeded from clean with Lean `leanprover/lean4:v4.33.1`, Mathlib v4.33.1 rev `0df444a360` (prebuilt pool `poolM10`); 8708 jobs, **zero errors, zero warnings**.
- Axioms: fresh `lake env lean Check.lean` on the shipped project printed `[propext, Classical.choice, Quot.sound]` — only the three standard axioms — for the decisive theorem `double_gap_law_false` and all supporting lemmas (`compl_ne_double_gap`, `Ioo_one_two_not_component`, `Ioo_neg_two_neg_one_not_component`, `Ioo_one_two_not_component_in_Icc`, `Ioo_one_two_not_subset_hull`, `one_mem_cantorSet`, `sub_subset_Icc`, `sSup_sub`, `sInf_sub`). No `sorry`, `native_decide`, `admit`, `implemented_by`, `extern`, `unsafe`, or declared `axiom` anywhere in the submission.
- Aux code: `verification/axioms.txt` and `verification/build.txt` match my fresh runs exactly. `verification/SHA256SUMS.txt` has one stale entry (`conjecture.md`, re-checksummed before the official copy swap); all other 13 entries verify. Not blocking.
- Metadata: `metadata.csv` lists 00000008330 with `proven=false, disproven=false` (unsolved) — consistent.

## Semantic audit

The official conjecture is a three-clause conjunction about arithmetic sums of Cantor sets; its second clause (the "double gap law") states that "the complete list of gaps of the difference set C − C (complement intervals) is the double gap (−2,−1) ∪ (1,2)". The submission's decisive theorem `C8330.double_gap_law_false` is the conjunction of the negations of this clause under every natural reading: (R1) the complement of C − C is not (−2,−1) ∪ (1,2); (R2) neither (1,2) nor (−2,−1) is a bounded connected component of ℝ∖(C−C) (formalized as the `IsGap` predicate: a component of the complement that is bounded); (R3) (1,2) is not a component of [−2,2]∖(C−C); (R4) (1,2) is not even contained in the hull [inf(C−C), sup(C−C)] = [−1,1]. Refuting this necessary second clause falsifies the conjunction, exactly as a disproof should; the dimension-sum and Newhouse clauses need not be assessed.

The formalization is faithful in the strongest sense: `C` is Mathlib's actual `cantorSet` (the intersection of the iterated middle-third removals), the difference set is the genuine pointwise subtraction `{x − y | x, y ∈ C}`, and components are Mathlib's `connectedComponentIn`. The proof uses only C ⊆ [0,1] (Mathlib `cantorSet_subset_unitInterval`) and 0, 1 ∈ C (1 = (2+1)/3 lies in every pre-Cantor set, proved by induction). Hence C − C ⊆ [−1,1] with both endpoints attained, so sup = 1 and inf = −1; (1,∞) and (−∞,−1) lie in the complement; the component of any point of (1,2) contains (1,∞), hence 3 ∉ (1,2) — contradiction; and 3/2 ∉ [−1,1]. Every step is elementary and verified by the kernel. (For context, the true state of affairs is even more decisive: C − C = [−1,1] since C is symmetric about 1/2, so C − C has no gaps at all — the double-gap list was never plausible; the submission does not need this fact and correctly does not formalize it.)

The quantifier structure is right: the R2 theorems hold for every x (not merely some), making them stronger than needed; the counterexample reasoning (3 ∈ complement ∖ ((−2,−1) ∪ (1,2))) is a genuine witness for R1. No hypotheses are strengthened and no definition is rigged: `IsGap` is the standard bounded-complementary-component notion, and the four readings are enumerated honestly, with the report explicitly noting the one uncovered exotic reading (complement relative to some other ambient set such as (1,2) itself, under which the clause would not even be about C − C's gaps in the line). This is a valid disproof of a conjecture clause that is simply false.

## Issues found

None blocking. Stale entry in `verification/SHA256SUMS.txt` (`conjecture.md`); the shipped copy is byte-identical to the official file.

## Verdict

APPROVED. A clean, fully machine-checked disproof of the double-gap clause: the middle-thirds Cantor difference set lies in [−1,1] and attains both endpoints, so (1,2) and (−2,−1) are not gaps of C − C under the complement, component, ambient-interval, or hull reading. Formalization uses the real Cantor set and real pointwise subtraction, build is clean, axioms are only the standard three, and the report matches the Lean exactly.
