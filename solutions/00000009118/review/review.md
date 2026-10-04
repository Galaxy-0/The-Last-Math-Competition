# Solution Review — Conjecture 00000009118 (PR 395)

**Submission:** ziangni-sys — `ziangni-sys_submission_20261004040827`
**Reviewer:** competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-04

## Checklist results
- Conjecture read: yes — "The size of the finite field analogue of Kakeya sets has the explicit lower bound q^n" (disproof submission).
- LaTeX: pdflatex twice, exit 0 both passes, 0 errors; shipped report.pdf is a genuine 2-page PDF matching report.tex (title, table of lines, all sections verified by text extraction).
- Lean build: `lake build` exit 0, "Build completed successfully", no warnings; three `#print axioms` lines all [propext, Classical.choice, Quot.sound].
- Forbidden content: grep over lean/Main.lean and lakefile.lean — no hits. Finite checks use kernel-checked `decide` (NOT native_decide).
- Auxiliary code: none needed; verification.txt claims match my independent build and audit. Hand re-derivation of the counterexample: F_2^2 \ {(0,0)} = {(1,0),(0,1),(1,1)}; lines: v=(1,0),a=(0,1) → {(0,1),(1,1)}; v=(0,1),a=(1,0) → {(1,0),(1,1)}; v=(1,1),a=(1,0) → {(1,0),(0,1)}; all ⊆ K, all 3 nonzero directions covered, |K|=3 < 4 = q^n. Confirmed.
## Semantic audit
Conjecture literal claim (EN): "The size of the finite field analogue of Kakeya sets has the explicit lower bound q^n." (CN: 其有限域模拟的 Kakeya 的大小为 q^n 的显式下界.) Neither version supplies a multiplicative constant or excludes small fields, so the asserted bound is |K| ≥ q^n with coefficient 1 — equivalent to claiming every Kakeya set is the entire ambient space, which is maximally strong.

Lean encodings (namespace `FiniteKakeya9118`):
- `abbrev Point := Fin 2 → ZMod 2` — the actual vector space F_2^2 with Mathlib's field instance (`scalar_field : Nonempty (Field (ZMod 2))`, `field_card : Fintype.card (ZMod 2) = 2`).
- `def affinePoint (a v : Point) (t : ZMod 2) : Point := a + t • v` — standard affine-line parameterization with actual field operations.
- `def IsKakeya (K : Finset Point) : Prop := ∀ v : Point, v ≠ 0 → ∃ a : Point, ∀ t : ZMod 2, affinePoint a v t ∈ K` — the standard Kakeya condition: a full line in EVERY nonzero direction. Faithful.
- `def puncturedPlane : Finset Point := Finset.univ.erase 0` — K = F_2^2 minus the origin.

Theorems: `theorem puncturedPlane_isKakeya : IsKakeya puncturedPlane` (full quantified predicate, kernel-checked by decide, not an assumed incidence table); `theorem affinePoint_injective : ∀ a v : Point, v ≠ 0 → Function.Injective (affinePoint a v)` — rules out the vacuity concern that a "line" could degenerate to a single point; every line really has q = 2 distinct points. Final: `theorem conjecture_00000009118 : IsKakeya puncturedPlane ∧ puncturedPlane.card < Fintype.card (ZMod 2) ^ (2 : ℕ)` (3 < 4, with q^n literally rendered as card(F_q)^n), and `theorem universal_bound_false : ¬ (∀ K : Finset Point, IsKakeya K → Fintype.card (ZMod 2)^2 ≤ K.card)` — explicit negation of the universal bound in this ambient space, which suffices to refute the bound "for all finite fields and dimensions."

Non-vacuousness: the Kakeya property is genuinely satisfied (all 3 nonzero directions, both scalar values, all points in K), the inequality is strict, and the ambient cardinality is checked separately (ambient_card = 4). Mathematically this is decisive, not a technicality: the coefficient-1 bound would force K = F_q^n always; the true optimal bounds are of the form c_n q^n with c_n < 1, as the report honestly notes (it explicitly does not dispute c_n q^n bounds).
## Issues found
Edge-case flag (non-blocking, for coordinator awareness): the counterexample uses the smallest field q=2, n=2. The conjecture text carries NO restriction on q or n and no constant c_n, so under the literal-statement precedent the disproof is valid; the report transparently acknowledges scope.
## Verdict rationale
The Lean project builds cleanly with only standard axioms, encodes the standard finite-field Kakeya definition faithfully over the actual field F_2 with genuine line injectivity (no degenerate-line vacuity), and establishes a hand-verified strict counterexample |K| = 3 < 4 = q^n satisfying the full Kakeya condition. The literal coefficient-one lower bound is refuted; LaTeX/PDF/verification evidence are consistent. Approved with the small-field edge-case flag noted above.

## Disposition
APPROVED — merged into main (PR 395). Independent fresh rebuild of the Lean project (Mathlib-pinned, exit 0; only standard foundational axioms; no sorry/native_decide/extra axioms), LaTeX recompilation, auxiliary-script re-runs where shipped, independent recomputations, and a semantic audit confirming the Lean theorem establishes or refutes the conjecture as stated in both language versions.
