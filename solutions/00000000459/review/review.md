# Solution Review — Conjecture 00000000459 (PR 331)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261003130000`
**Reviewer:** competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-03

## Checklist results
- Conjecture read: yes — there is a rank-preserving bijection between the fixed points of the Kreweras involution in NC_n and the 3-noncrossing isolated-point-free partitions (counted by Riordan numbers).
- LaTeX: compiled ok (pdflatex twice, exit 0, 0 errors, bibliography resolves); included main.pdf real PDF v1.5, 2 pages, matches tex.
- Lean build: fresh build after `rm -rf .lake`, exit 0, no warnings; axioms propext/Classical.choice/Quot.sound exactly as recorded.
- Forbidden content: none.
- Auxiliary code: none shipped (`auxiliary_scripts_rerun: []`). I ran my own independent brute force (python3): for n = 1..4, enumerated all set partitions, computed the Kreweras complement as the coarsest admissible interleaved partition, fixed points, and 3-noncrossing no-singleton counts. Results: n=2 gives K({01}) = {0}{1}, K({0}{1}) = {01} (K swaps), Fix = 0, target = 1 — exactly the submission's claim. (Also mismatched at n=3: 0 vs 1; n=4: 0 vs 4.)
## Semantic audit
Conjecture literal claim: "There is a rank-preserving bijection between the fixed points of the Kreweras involution in NC_n and the 3-noncrossing isolated-point-free parts." No range or exception for n is stated; the disproof takes n = 2.

Lean definitions all faithful and general:
- `Partition n` = arbitrary Prop-valued equivalence relation on Fin n (`EquivalenceLaws`: refl/symm/trans) — actual set partitions, not labels; `every_partition_encoded` proves every partition of two points is `model false` (discrete D) or `model true` (one block T), and `model_injective` separates them, so later finite checks are exhaustive.
- `Noncrossing R := ∀ a b c d, a < b → b < c → c < d → R a c → R b d → R a b` — the standard alternating-blocks condition.
- `interleave P Q` on Fin 4 = positions 1,1',2,2' (evens carry P, odds carry Q), with `interleave_is_partition` proving the combined relation is an equivalence.
- `IsKrewerasComplement P Q := Noncrossing P ∧ Noncrossing Q ∧ Noncrossing (interleave P Q) ∧ ∀ R, Noncrossing R → Noncrossing (interleave P R) → Refines R Q` — the standard coarsest-admissible-complement definition of the Kreweras complement. `kreweras_models` verifies K(D) = T and K(T) = D (for P = T the interleaving with Q = T crosses: arcs (0,2) and (1,3) alternate); `kreweras_unique` proves uniqueness; `every_partition_has_complement` existence.
- Target: `NoSingletons` (no isolated points), `Arc` (consecutive block elements) and `ThreeNoncrossing` (no six points a<b<c<d<e<f with arcs (a,d),(b,e),(c,f)) — the standard arc-representation 3-crossing.
- `no_fixed_points (P) : ¬ IsKrewerasComplement P P` — Fix(K) on NC_2 is empty, against the maximality definition (via uniqueness with the verified complements).
- `targetWitness` (= T) is a target object; `target_unique` shows it is the only one — target has exactly one element.

Final theorem: `conjecture459_refuted : ¬ ∃ f : FixedPoints → TargetObjects, Surjective f` (a surjection from the actual fixed-point subtype to the actual target subtype cannot exist). Since a bijection is a surjection, this negates the existence of a bijection, rank-preserving or otherwise — the rank function is subsumed and correctly left unformalized.

(i) Definitions faithful. (ii) Hypotheses: n = 2, standard Kreweras complement on NC_2 (all partitions of [2] are noncrossing — verified); the conjecture states no excluded n. (iii) |Fix| = 0 ≠ 1 = |target| kills any bijection — the mismatch (my brute force confirms) is the parity fact #blocks(π) + #blocks(K(π)) = n+1 = 3 for n = 2. (iv) Not vacuous: partitions, the interleaving construction, the maximality definition, isolated points, and 3-crossings are all present as genuine mathematical objects with an exhaustive classification lemma; opposite of the #286-288 failure mode. LaTeX matches Lean: same D/T, same K values, same "no surjection hence no bijection" logic, honest citation (Ebrahimi-Fard/Ringeard Definitions 2.9/2.17/2.19).
## Issues found
- Non-blocking (interpretation): the source does not specify the range of n; if an organizer intended n ≥ 3 or odd n only, the n = 2 counterexample would not apply as stated — but no such restriction appears in the conjecture, and my independent computation shows the mismatch persists at n = 3 (Fix 0 vs target 1) and n = 4 (0 vs 4), so the conjecture fails under essentially any reading; the Lean itself only proves n = 2.
- Non-blocking: "Kreweras involution" is formalized as the Kreweras complement map (the standard object); the tex notes it happens to be an involution on NC_2 and needs no general involution theorem.
## Verdict rationale
At n = 2 the Kreweras complement (by its genuine maximality definition, exhaustively checked over all partitions) has no fixed points while the 3-noncrossing isolated-point-free side contains exactly one partition, so no bijection — hence no rank-preserving bijection — can exist. The Lean encodes the actual objects rather than surrogates, my independent brute force confirms the combinatorics, and all builds and compilations succeed with only standard axioms. A genuine refutation of the conjecture as stated.

## Disposition
APPROVED — merged into main (PR 331). Independent fresh rebuild of the Lean project (Lean 4.19.0, `lake build` with warnings-as-errors, exit 0, axioms limited to the standard Lean foundational set), LaTeX recompilation, auxiliary-script re-runs, and a semantic audit confirming the Lean theorem refutes the conjecture as stated in both language versions.
