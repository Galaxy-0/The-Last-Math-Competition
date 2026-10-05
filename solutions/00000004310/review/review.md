# Solution Review — Conjecture 00000004310 (PR 584)

**Submission:** jilint777 — `jilint777_submission_20261004192508`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-04

## Checklist results
- Official bilingual conjecture read (`conjectures/00000004310.md`): the claim is that there exist two imaginary quadratic fields of the same discriminant whose class-group 3-parts are isomorphic while their unit groups are not, and that the smallest such discriminant is a seven-digit value.
- LaTeX report independently rebuilt with `latexmk -pdf`: clean; text identical to the shipped `report.pdf` after bullet-glyph normalization.
- Lean: fresh `lake build` on `leanprover/lean4:v4.19.0`, zero errors/warnings; build log identical to `verification.txt`.
- `#print axioms` (Main.lean lines 670–682): only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`/`native_decide`/`axiom`/`unsafe`/`implemented_by`/`extern`/`admit`.
- `verify.py` rerun: 21 PASS, 0 FAIL; output identical to `verification.txt` except the trailing wrapper `exit 0`. It checks disc injectivity on 12160 squarefree `m`, the fundamental-discriminant structure, brute-force unit counts, the Pell-type equation `t² − Du² = 4`, automorph counts of 143695 reduced binary quadratic forms, and the real-field readings.
- Independent verification (reviewer's own code): `disc` injective on all 3041 squarefree `m < 0` with `|m| ≤ 5000` (zero collisions); unit counts of the orders of discriminants −3, −4, −7, −8, −11, −19, −43, −67, −163 computed by solving `a² + tab + nb² = 1` give exactly 6, 4, 2, 2, … units — precisely `w(D)`.

## Semantic audit
The conjecture's existential clause (E) demands two imaginary quadratic fields with *equal discriminant*, isomorphic class-group 3-parts, and *non-isomorphic* unit groups. The refutation is elementary and correct: an imaginary quadratic field is `Q(√m)` for a unique squarefree `m < 0`, its discriminant is `disc m = m` if `m ≡ 1 (mod 4)` and `4m` otherwise, and this map is injective (if `m₁ ≡ 1` and `m₂ ≢ 1 (mod 4)` then `m₁ = 4m₂ ≡ 0 (mod 4)`, a contradiction; the other cases are immediate). Hence two imaginary quadratic fields of the same discriminant are equal, so their unit groups are equal and certainly isomorphic — the witness set is empty, and clause (M) (the seven-digit minimum) fails because there is no witness discriminant at all. A second, independent argument covers orders and forms: the unit group of the imaginary quadratic order of discriminant `D` is cyclic of order `w(D) ∈ {2, 4, 6}` (`μ₂`, `μ₄` for `D = −4`, `μ₆` for `D = −3`), a function of `D` alone, so equal discriminants give isomorphic unit groups regardless of any classification of fields.

The Lean formalization is faithful. Fields are parametrized by squarefree `m < 0` (`IsImagQuadParam`), the discriminant `disc` is defined exactly as in the official statement, the class-group condition is left as a completely arbitrary predicate `C3` (correct: it is a conjunct of the existential, and refuting the existential for every `C3` refutes it for any conceivable reading of "3-parts of the class groups are isomorphic"), and the non-isomorphism condition is the negation of `MulIso` between the actual unit groups (subtypes of the modeled rings of integers, with multiplicative bijections). Two independent machine-checked proofs of `conjecture_00000004310_false` are given (via `disc_injective`; via `w`), plus `no_witness_discriminant`, `smallest_seven_digit_false`, and the orders reading (`order_claim_false`). Non-vacuity is demonstrated (`fieldUnits_not_iso`: `O_{−1}^× ≇ O_{−2}^×` by a pigeonhole argument, so "not isomorphic" is a satisfiable condition), and the honest disclosure that if the words "of the same discriminant" are dropped, witnesses do exist but have one-digit discriminants (`−4`, `−8`, both class number 1), so clause (M) fails under every reading. The units classification (`units_classification`, `unitList_eq_pows`) is proved from scratch via the norm identity `4N = (2a+tb)² + (4n−t²)b²`, bounding `|a|, |b| ≤ 1`, and enumerating the nine cases — the standard proof.

The bridge facts (F1)–(F4) (classification of quadratic fields, shape of the maximal order, discriminant formula, uniqueness of orders) are standard (Marcus, Cox); Lean proves the integer part of (F2) (`integral_iff`, `halfCoords_mul`) and the discriminant formula as a determinant of the trace form, and the report supplies the remaining elementary uniqueness argument. My independent computations confirm both pillars (injectivity and the `w(D)` classification).

## Issues found
None blocking.

## Verdict
APPROVED. The disproof is mathematically airtight (the discriminant determines an imaginary quadratic field, and the unit group is `Z/w(D)`, a function of the discriminant), formalized from scratch with two independent Lean proofs and only the three standard axioms, with all readings (orders, forms, |D|, dropped conditions, real fields) honestly analyzed, and all artifacts reproducing exactly.
