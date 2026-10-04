# Solution Review — Conjecture 00000008557 (PR 380)

**Submission:** ziangni-sys — `ziangni-sys_submission_20261004030420`
**Reviewer:** competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-04

## Checklist results
- Conjecture read: yes — claims (a) #subdirectly-irreducible factors ≥ #atoms of Con(L) and (b) #atoms of Con(L) ≤ log₂|L| for a lattice L.
- LaTeX: compiled (pdflatex twice, exit 0 both passes); shipped report.pdf is a real PDF (v1.5) whose extracted text matches report.tex content.
- Lean build: exit 0, "[1730/1731] Built Main", "Build completed successfully.", zero warnings/errors; axiom audit lists only [propext, Classical.choice, Quot.sound] for `congruences_classified`, `actual_atom_count`, `conjecture_00000008557_false`.
- Forbidden content: none. Grep hits only English prose asserting absence ("No supplied atom count, ... admitted proofs, or native decision shortcuts are used", report.tex:45); no tactic-level `sorry`/`admit`, no `native_decide`, no `axiom` decl, no `unsafe`/`extern`/`implemented_by`/`skipKernelTC`. `set_option maxHeartbeats/maxRecDepth` bumps only (do not weaken kernel checking).
- Auxiliary code: `python3 verify.py` → exit 0, output byte-identical to verification/python.txt ("PASS: all 512 relation tables tested ... 3<4 ..."); verification/lean-check.txt and lean-build.txt match my own build output exactly. I additionally re-enumerated all 512 relations with independently written code: exactly 4 congruences of C₃, exactly 2 atoms, log₂3 = 1.5849... < 2.
## Semantic audit
Conjecture (EN): "The lower bound on the number of subdirectly irreducible factors of a lattice is the number of atoms of its congruence lattice; and the upper bound on the atom count is log_2 |L|." (CN: "原子个数的上界为 log₂|L|"). "The atom count" refers anaphorically to "the number of atoms of its congruence lattice", so the disputed conjunct is the universal claim #atoms(Con L) ≤ log₂|L|. The submission refutes this conjunct; since the conjecture is conjunctive, that suffices, and the README/report say so explicitly.

Lean encodings (all faithful, nothing assumed as data):
- `abbrev Chain := Fin 3` with the genuine Mathlib `Lattice` instance (`example : Lattice Chain := inferInstance`); meet/join are `min`/`max`.
- `def IsCongruence (r : Relation) : Prop` — reflexivity + symmetry + transitivity + two-argument compatibility with BOTH `min` and `max` — the textbook lattice-congruence definition on Boolean truth tables (complete finite model: all 3×3 relations are truth tables).
- `theorem congruences_classified : ∀ r : Relation, IsCongruence r → r = bottom ∨ r = alpha ∨ r = beta ∨ r = top := by decide` — kernel-checked exhaustive classification of all 512 relations; Con(C₃) = {Δ, α, β, ∇}, α = collapse {0,1}, β = collapse {1,2}.
- `def IsAtom (r : Relation) : Prop := IsCongruence r ∧ r ≠ bottom ∧ ∀ s, IsCongruence s → Below s r → s = bottom ∨ s = r` — literal atom in the inclusion order of congruences.
- `theorem actual_atom_count : atoms.card = 2` — proved via `atoms_classified : IsAtom r ↔ r = alpha ∨ r = beta` (both directions proved, incl. `top_not_atom`).
- `theorem logTwo_three_lt_two : logTwo 3 < 2` — proved from `Real.log` strict monotonicity (log 3 < log 4 = 2 log 2, divide by log 2 > 0).
- `theorem conjecture_00000008557_false : ¬ ((atoms.card : ℝ) ≤ logTwo (Fintype.card Chain))` — negates the literal bound 2 ≤ log₂3.

(i) Definitions faithful: yes, genuine lattice-congruence and atom definitions, real logarithm. (ii) No side hypotheses to satisfy — C₃ is a legitimate lattice. (iii) 2 > log₂3 contradicts the claimed upper bound. (iv) Not vacuous: the classification and atom count are proved, not hypothesized; `decide` is kernel-verified (not `native_decide`). Alternative reading check: the only other grammatical reading (atoms of L itself: C₃ has 1 atom ≤ log₂3, no contradiction) is ruled out by the first clause, which explicitly names "atoms of its congruence lattice" as the counted quantity; the submission's reading is the literal one. The disproof is also robust to a floor/integer-log reading? floor(log₂3) = 1 < 2 — still violated; the report explicitly addresses that the real log is used, and even the integer-part reading fails.
## Issues found
none blocking
## Verdict rationale
The atom-count upper bound #atoms(Con L) ≤ log₂|L| is genuinely false (truth for direct decompositions involves only central congruences, not all atoms), and C₃ with its 2 congruence atoms vs log₂3 ≈ 1.58 is the canonical minimal counterexample, fully formalized with a kernel-checked exhaustive classification. All quantities (congruence list, atom set, cardinality, real log inequality) are proved in Lean from Mathlib definitions with only standard axioms, and the independent Python enumeration agrees. This is a complete formal disproof, not a numeric-facts-only argument.

## Disposition
APPROVED — merged into main (PR 380). Independent fresh rebuild of the Lean project (exit 0; only standard foundational axioms; no sorry/native_decide/extra axioms), LaTeX recompilation, auxiliary-script re-runs where shipped, independent recomputations, and a semantic audit confirming the Lean theorem establishes or refutes the conjecture as stated in both language versions.
