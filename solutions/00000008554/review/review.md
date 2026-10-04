# Solution Review — Conjecture 00000008554 (PR 365)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261003215646`
**Reviewer:** competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-04

## Checklist results
- Conjecture read: yes — "The homological dimension of the crosscut complex equals the rank of the lattice minus 1; and its Euler characteristic is the Mobius number" (bilingual).
- LaTeX: recompiled twice in /tmp/tlmc-review2/scratch/pr-365, pdflatex exit 0, zero errors; shipped main.pdf is a real 2-page PDF whose SHA-256 (eb801bd9…) matches VALIDATION.json and whose text matches main.tex.
- Lean build: fresh `rm -rf .lake && lake build` exit 0; only output lines are the three `#print axioms` infos (propext, Classical.choice, Quot.sound — standard); lakefile sets `-DwarningAsError=true`; toolchain lean4:v4.19.0, no external deps (Std only).
- Forbidden content: grep for sorry/admit/native_decide/`axiom `/unsafe/implemented_by/extern/skipKernelTC over lean/Main.lean: no matches. `#print axioms conjecture8554_counterexample` = [propext, Classical.choice, Quot.sound].
- Auxiliary code: no Python shipped (none needed — computation done by Lean `decide` over exhaustive finite codes); verification/ logs match fresh build output; conjecture.md byte-identical to official file (sha256 ae03613b… matches SOURCE.md pin).
## Semantic audit
Conjecture claim: for a (finite) lattice, hd(crosscut complex) = rank − 1 (plus Euler = Möbius clause). Submission exhibits B2 = {0,a,b,1} encoded as `E := Fin 4` with `below x y := x=0 ∨ y=3 ∨ x=y`; `lattice_laws` proves reflexive/antisym/trans + meet/join universal properties by decide. `lattice_rank_two` proves max chain size = 3 over ALL 16 subsets and transfers to arbitrary predicate subsets via `all_prop_families`. The crosscut C={1,2} is verified a genuine crosscut (`genuine_crosscut`: proper antichain meeting every maximal chain, lifted to predicates by `every_actual_maximal_chain_meets_crosscut`) — matching the conjecture's definition "a crosscut is a transversal [of maximal chains]". The face predicate `Face s := meetFace s ≠ 0 ∨ joinFace s ≠ 3` is tied to the lattice's actual meet/join by universal-property certificates (`face_meet_and_join_are_genuine`), giving faces {∅,{a},{b}} (`complete_face_list`), i.e. two isolated vertices (S^0), since a∧b=0 and a∨b=1. Chains: `ChainGroup n := Simplex n → Int` with `Simplex n = {s // Face s ∧ faceSize s = n+1}` — full free abelian groups, no truncation; `no_positive_simplices` for every n, `boundary_forced` proves any zero-preserving boundary candidate is the zero map, so boundaries/images are the genuine ones. Final theorem:
```lean
theorem conjecture8554_counterexample :
    HomologicalDimension false 0 ∧ HomologicalDimension true 0 ∧
    ¬HomologicalDimension false (2-1) ∧ ¬HomologicalDimension true (2-1)
```
with `higher_homology_zero : ∀ n, HomologyZero reduced (n+1)` for all n — together: sup{n : H_n ≠ 0} = 0 in BOTH ordinary and reduced integral homology, while rank − 1 = 2 − 1 = 1. I re-derived this independently by hand: B2's atom crosscut complex is S^0, H_0 = Z², H̃_0 = Z, all higher homology 0; homological dimension 0 ≠ 1. Euler clause honestly handled: `euler_conventions` proves χ = 2 ≠ 1 = μ(0,1) (ordinary, so the conjunct fails too) while χ̃ = 1 = μ; Möbius function verified by recurrence + uniqueness (`actual_mobius_recurrence`, `actual_mobius_unique`). Not vacuous: real lattice, real crosscut complex, real homology groups; engages the conjecture's actual objects, unlike the rejected PRs #286-288 pattern.
## Issues found
- Minor (non-blocking): `HomologicalDimension d` packages "H_d ≠ 0 ∧ H_n = 0 for n < d" and does not itself assert vanishing above d; the standard "largest nonzero degree" reading additionally needs H_n = 0 for n ≥ 1, which IS proven separately (`higher_homology_zero`, all n). Also, the submission's INDEPENDENT_REVIEW.md references a `check_8554.py` "saved beside this review" that is not present in verification/ — an author-side artifact gap only; no Python is required by the argument.
## Verdict rationale
The Lean project freshly builds warning-free with no sorry/axiom/native_decide, the PDF is real and recompiles, and the formalization faithfully encodes B2, its rank-2, its atom crosscut, and the genuine simplicial homology of the two-point crosscut complex in all degrees and both conventions. The final theorem directly contradicts the conjectured identity hd = rank − 1 at B2 (0 ≠ 1), and the Euler convention issue is transparently analyzed rather than hidden. This is a complete, non-vacuous disproof.

## Disposition
APPROVED — merged into main (PR 365). Independent fresh rebuild of the Lean project (exit 0, warnings-as-errors where set, only standard foundational axioms), LaTeX recompilation, auxiliary-script re-runs, and a semantic audit confirming the Lean theorem establishes or refutes the conjecture as stated in both language versions.
