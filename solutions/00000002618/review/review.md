# Solution Review — Conjecture 00000002618 (PR 333)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261003130000`
**Reviewer:** competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-03

## Checklist results
- Conjecture read: yes — a finite lattice is semidistributive iff every element has a unique canonical join representation (plus a congruence-separation clause); submission refutes the "canonical join ⇒ semidistributive" direction.
- LaTeX: compiled ok (pdflatex x2, exit 0, 0 errors); shipped main.pdf is a real PDF v1.5, 2 pages, size 50 KB, matching the recompiled output (2 pages) and verification.json ("pages": 2); shipped-pdf SHA256 matches the recorded hash.
- Lean build: fresh `rm -rf .lake && lake build` exit 0, "Build completed successfully", with `-DwarningAsError=true` in lakefile.toml; toolchain leanprover/lean4:v4.19.0; no warnings.
- Forbidden content: none — no `sorry`, no tactic `admit`, no `native_decide`, no `axiom` declarations, no `unsafe`/`@[implemented_by]`/`extern`. `#print axioms` shows only [propext, Classical.choice, Quot.sound].
- Auxiliary code: `node independent-check.js` exit 0; its output is byte-identical to the recorded stdout in auxiliary-results.json (only a trailing newline differs in my capture) and to independent-check.json. All SHA256 hashes in verification.json match the on-disk files, including Main.lean.
- Folder name: `gaochengzhecpu_submission_20261003130000` — matches the 14-digit-timestamp pattern.
## Semantic audit
Conjecture (English): "A finite lattice is semidistributive if and only if every element has a unique canonical join representation." Key Lean definitions, all faithful:
- `LatticeData V` = partial order (refl/antisymm/trans) + bottom + binary join and binary meet with both universal properties — exactly a lattice in the standard sense; the instance `seven : LatticeData (Fin 7)` has every axiom kernel-checked by `decide`.
- `JoinRep D w S` = S's elements are ≤ w and w is ≤ every common upper bound of S — exactly w = ⋁S, for arbitrary `S : V → Prop` (not a coded family); `every_subset_encoded` + `checked_encoding` prove every predicate-valued subset has a binary code, so the finite checks cover all subsets.
- `CanonicalJoin D w S` = `Irredundant D w S ∧ ∀ T, Irredundant D w T → Refines D S T` — the standard definition (irredundant and join-refining every irredundant representation; in fact `Certificate` checks refinement against every join representation, which is stronger).
- `Semidistributive D` = `JoinSemidistributive D ∧ MeetSemidistributive D` with the two standard implications — the standard two-sided meaning, consistent with both the English and Chinese statements (半分配).
Final theorems:
- `counterexample : AllUniqueCanonical seven ∧ ¬Semidistributive seven`
- `conjecture2618_false : ¬ClaimedCriterion` where `ClaimedCriterion : ∀ n, ∀ D : LatticeData (Fin n), AllUniqueCanonical D → Semidistributive D`.
The lattice is B({a,b,c}) minus {b,c} (7 elements; join = union except B∨C = 1). Uniqueness of canonical join representations is proved in general (`canonical_unique` via `irredundant_antichain`), existence per element by kernel-checked certificates with `rep` codes {0,2,4,6,16,18,20} matching the report's table. Meet-semidistributivity fails at x=A, y=B, z=C: A∧B = 0 = A∧C but A∧(B∨C) = A ≠ 0 (`not_meet_semidistributive`, witnesses 1, 2, 4). This contradicts the conjecture's ⟸ direction. The counterexample satisfies the hypothesis (finite lattice, unique canonical join reps for every element) and violates the conclusion (not semidistributive); it is not vacuous — the lattice, the representations over all predicates, and both SD laws are the conjecture's actual objects. The independent JS enumeration (raw subset masks, independent of Lean's definitions) confirms: exactly 1 canonical representation per element, 0 join-SD failures, 2 meet-SD failures ([1,2,4] and [1,4,2]). LaTeX math matches the Lean exactly (same 7-element lattice, same Can(w) table, same failing triple A,B,C). The unused "congruence separation with separation constant 1" clause cannot rescue the already-refuted biconditional conjunct, as the report argues.
## Issues found
- Interpretation-dependent (non-blocking): the disproof requires the standard two-sided reading of "semidistributive" (both join- and meet-SD). Under a one-sided join-SD-only reading the counterexample would not apply (the lattice IS join-SD, as the Lean separately proves and the report discusses). Standard references (e.g., Freese–Jezek–Nation, Barnard) and the Chinese 半分配 both support the two-sided reading, and SOURCE.md states the interpretation openly. The true finite-lattice theorem (JD ⟺ canonical join representations) is respected, not misquoted.
## Verdict rationale
Everything compiles and runs from scratch with warnings-as-errors, no forbidden content, hashes match, and the auxiliary enumeration independently reproduces the combinatorics. The Lean definitions faithfully encode lattices, canonical join representations over arbitrary subsets, and two-sided semidistributivity; the 7-element lattice is a genuine, non-vacuous counterexample to the "canonical join representations imply semidistributivity" direction under the standard terminology shared by both language versions of the conjecture. This is a real disproof of the conjecture as stated.

## Disposition
APPROVED — merged into main (PR 333). Independent fresh rebuild of the Lean project (Lean 4.19.0, `lake build` with warnings-as-errors, exit 0, axioms limited to the standard Lean foundational set), LaTeX recompilation, auxiliary-script re-runs, and a semantic audit confirming the Lean theorem refutes the conjecture as stated in both language versions.
