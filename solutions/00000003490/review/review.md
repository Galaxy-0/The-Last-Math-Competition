# Solution Review — Conjecture 00000003490 (PR 308)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261003091740`
**Reviewer:** competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-03

## Checklist results
- Conjecture read: yes — there exist graph families with identical chromatic polynomial AND spectral radius but different chromatic numbers; minimal order of the separating family is ten (Schwenk-type branch pastings).
- LaTeX: compiled ok (pdflatex twice, exit 0, 1 page, 112 KB); included main.pdf is a real PDF (1 page, 34 KB, verified); tex and pdf agree.
- Lean build: fresh build after `rm -rf .lake`, exit 0, no warnings (warnings-as-errors active), v4.19.0, imports only Std.
- Forbidden content: none — no sorry/admit/native_decide/axiom/unsafe/implemented_by/extern; only maxRecDepth/maxHeartbeats (allowed). `#print axioms` for all three principal results: [propext, Classical.choice, Quot.sound] — standard only.
- Auxiliary code: none present (records `auxiliary_scripts_rerun: []`, consistent). All recorded sha256 file hashes match current files; official conjecture sha256 = original_source_sha256. Independent sanity check on six small graphs (K3, E3, P4, C4, K4−e, empty graph): χ equals min{k : P(k) > 0} in every case, including the χ = 0 empty-graph edge case matching the stated conventions.
## Semantic audit
Conjecture (literal): "There exist graph families with identical chromatic polynomial and spectral radius but different chromatic numbers." The decisive impossible content is: identical chromatic polynomial + different chromatic numbers. Classically χ(G) = min{k ∈ ℕ : P_G(k) > 0}, so P determines χ; the submission formalizes exactly this and refutes the existence of any such pair (hence also the "minimal order ten" and Schwenk clauses, which are moot once the existential clause fails).

Objects (all general, arbitrary finite graphs — vertices Fin n, arbitrary decidable edge relation, no bounded search): `Proper adj cs` is the proper-coloring predicate on color lists; `Colorable adj k` is standard k-colorability; `chromaticEvaluation adj k := (words k n).countP (decide ∘ Proper)` counts proper k-colorings, where `words k n` enumerates ALL length-n lists with entries < k with `mem_words` (completeness) and `words_nodup` (no double counting) proved by induction. The key theorem
`evaluation_pos_iff_colorable (adj) (k) : 0 < chromaticEvaluation adj k ↔ Colorable adj k`
is proved via `List.countP_pos_iff` + `mem_words` — sound and general. `ChromaticNumberIs adj r := Colorable adj r ∧ ∀ j < r, ¬Colorable adj j` is the honest least-k definition (covering the empty graph with χ = 0, as the tex states).

`equal_evaluations_equal_chromatic_numbers`: if `SameChromaticEvaluations G H` (∀ k, counting functions agree) then Colorable G k ↔ Colorable H k for every k, hence the least such k agree — g = h, by clean not_lt/not_gt reasoning. `not_separating_pair_claim : ¬SeparatingPairClaim` refutes the existence of two graphs with identical coloring-count functions and different chromatic numbers. Since the conjecture's pair must satisfy the extra spectral-radius condition, and dropping a conjunct only weakens the existential claim, refuting the weaker claim refutes the conjecture's — the Lean comment states this correctly.

Polynomial bridge: `polynomialEval p x` (Horner) evaluates integer coefficient lists; `IsChromaticPolynomial G p := ∀ k : Nat, polynomialEval p k = chromaticEvaluation G k` is precisely the defining counting characterization of the chromatic polynomial on natural points. `PolynomialSeparatingPairClaim` requires the SAME coefficient list p to be a chromatic polynomial of BOTH graphs (with different chromatic numbers), and `not_polynomial_separating_pair_claim` refutes it: shared p ⇒ equal evaluations at all naturals ⇒ equal χ. The formalization also covers any reasonable notion of "same polynomial": if two lists p1, p2 give equal values on all naturals and each satisfies the counting characterization for G resp. H, then p1 itself is a common witness, so the shared-list formulation loses no generality.

The theorem engages the conjecture's actual objects (proper colorings, coloring counts, chromatic polynomials, chromatic numbers) and is the exact negation of the conjecture's existential clause. Not vacuous and not a bounded-search trick — uniform in the number of vertices and colors. LaTeX/Lean match: same characterization P_G(k) = #proper k-colorings, same theorem names, same argument order.
## Issues found
- Minor (non-blocking): the conjecture's "spectral radius" and "asymptotic isomorphism of Schwenk-type branch pastings" clauses are not formalized; unnecessary, since the refuted polynomial/χ clause is the load-bearing impossibility and the rest is conjunctive decoration.
- Minor (non-blocking): the disproof shows the conjecture was ill-posed to begin with (chromatic number is functionally determined by the chromatic polynomial); this is a statement about the conjecture, not a defect of the submission.
## Verdict rationale
The submission compiles cleanly with no placeholders, proves a fully general theorem — for arbitrary finite graphs, identical chromatic polynomials (through the genuine counting characterization) force identical chromatic numbers — and thereby refutes the conjecture's central existential claim; the order-ten minimality and Schwenk clauses fail with it. The argument is the classical one, correctly formalized with exhaustive color-list enumeration and honest least-k definitions. A genuine, non-vacuous disproof.

## Disposition
APPROVED — merged into main (PR 308). Independent fresh rebuild of the Lean project (Lean 4.19.0, `lake build` with warnings-as-errors, exit 0, axioms limited to the standard Lean foundational set), LaTeX recompilation, auxiliary-script re-runs, and a semantic audit confirming the Lean theorem refutes the conjecture as stated in both language versions.
