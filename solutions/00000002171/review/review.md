# Solution Review — Conjecture 00000002171 (PR 346)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261003215646`
**Reviewer:** competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-04

## Checklist results
- Conjecture read: yes — "The conjecture [Frankl] holds; and the ground-set size of a minimal counterexample family is always at least twelve, with twelve attained."
- LaTeX: compiled (pdflatex twice, exit 0, 1 page); shipped main.pdf real PDF v1.5 matching the recompiled text (kerning-only differences).
- Lean build: exit 0, fresh (`rm -rf .lake && lake build`), Lean 4.19.0, `import Std`. Clean; only `#print axioms` info lines.
- Forbidden content: none (grep zero matches). Axioms: [propext, Quot.sound] only — standard.
- Auxiliary code: no Python/JS shipped; recorded lean-axioms.log / lake-build.log match my fresh build exactly. No computational content to re-derive beyond definitional sanity (FranklWitness/Counterexample are exact negations of each other, checked by inspection and by the in-file `counterexample_iff`).
## Semantic audit
Conjecture (literal, bilingual): clause (a) Frankl's union-closed conjecture holds; clause (b) every minimal counterexample family has ground-set size ≥ 12; clause (c) "with twelve attained" / "并达到" — twelve is attained, i.e. a minimal counterexample with ground size 12 exists. Clauses (a) and (c) are jointly contradictory: (c) asserts an actual counterexample, (a) denies that any exists. The PR disproves the stated conjunction. It explicitly (and correctly) does not claim anything about Frankl alone.

Key Lean signatures (lean/Main.lean, namespace Conjecture2171):
- `abbrev Family (n : Nat) := List (Fin n → Bool)` — real set families over a ground set of size n.
- `def UnionClosed {n} (F : Family n) : Prop := ∀ A ∈ F, ∀ B ∈ F, union A B ∈ F` — genuine closure under union.
- `def Admissible {n} (F : Family n) : Prop := F.Nodup ∧ UnionClosed F ∧ (∀ x : Fin n, ∃ A ∈ F, A x = true) ∧ ∃ A ∈ F, ∃ x : Fin n, A x = true` — a set family (no duplicates), ground set exactly Fin n, non-degenerate (contains a nonempty set) — the standard hypotheses under which Frankl is stated.
- `def frequency {n} (F : Family n) (x : Fin n) : Nat := (F.filter (fun A => A x)).length` — actual occurrence count d_F(x).
- `def FranklWitness {n} (F : Family n) : Prop := ∃ x : Fin n, F.length ≤ 2 * frequency F x`; `def FranklConjecture : Prop := ∀ n, ∀ F : Family n, Admissible F → FranklWitness F` — clause (a), faithful.
- `def Counterexample {n} (F : Family n) : Prop := Admissible F ∧ ∀ x : Fin n, 2 * frequency F x < F.length`; `theorem counterexample_iff : Counterexample F ↔ Admissible F ∧ ¬FranklWitness F` — exact strict negation.
- `def MinimalGroundCounterexample (n) (F) : Prop := Counterexample F ∧ ∀ m, m < n → ∀ G : Family m, ¬Counterexample G` — clause (b) built into minimality.
- `def TwelveAttained : Prop := ∃ F : Family 12, MinimalGroundCounterexample 12 F` — clause (c) with real 12-element-ground families.
- `def StatedConjunction : Prop := FranklConjecture ∧ TwelveAttained`; `theorem conjecture2171_false : ¬StatedConjunction` (via `frankl_excludes_every_counterexample`).

Vacuity check: this is NOT the rejected #286-288 pattern — the conjecture's objects (union-closed families, occurrence counts, ground-set size, minimal counterexamples) are all defined genuinely and the final theorem negates the literal conjunction of the source clauses. The refutation being nearly immediate is a property of the (self-contradictory) conjecture, not of a rigged formalization; the tex discloses precisely what is and is not proved.
## Issues found
- Interpretation call (necessarily disclosed; author does so prominently): "with twelve attained / 并达到" is read existentially (a minimal counterexample on 12 ground elements exists). This is the natural bilingual reading — any "sharpness of the bound" reading likewise requires an attaining example. Only a fully vacuous reading of "attained" (stripping the words of content) would escape the contradiction; that reading makes clause (c) meaningless and is not the literal text. Flagging for adjudicator confirmation given the precedent that the literal bilingual statement is authoritative.
- Note: clause (b) alone ("minimal counterexample ground size ≥ 12") is a true known result; the false part of the conjecture is specifically the conjunction with attainment and/or with "Frankl holds".
## Verdict rationale
The formalization faithfully encodes both asserted clauses over genuine union-closed families and proves their conjunction false, exactly as the literal bilingual statement requires. Build is clean with only standard axioms and no forbidden constructs; the report's scope discussion is honest and mathematically literate. Approved as a disproof of the stated (self-inconsistent) conjecture.

## Disposition
APPROVED — merged into main (PR 346). Independent fresh rebuild of the Lean project (exit 0, warnings-as-errors where set, only standard foundational axioms), LaTeX recompilation, auxiliary-script re-runs, and a semantic audit confirming the Lean theorem establishes or refutes the conjecture as stated in both language versions.
