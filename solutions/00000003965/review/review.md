# Solution Review — Conjecture 00000003965 (PR 325)

**Submission:** feiyuceng06-prog — `feiyuceng06-prog_submission_20261003112308`
**Reviewer:** competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-03

## Checklist
- [x] LaTeX source and PDF present
- [x] Lean 4 project compiles completely (lake build, exit 0, Mathlib v4.33.1)
- [x] No `sorry`, no `native_decide`, no extra axioms (`#print axioms` exactly `[propext, Classical.choice, Quot.sound]`)
- [x] Submission matches the conjecture's objects and literal statement

## Conjecture (verbatim summary)
Every graph G satisfies |box(G) − box(Ḡ)| ≤ 2 with respect to its complement, and the difference 2 is attained by an explicit construction.

## What the submission proves
The bound fails: for G = K_{2,2,2,2} (Mathlib's `completeEquipartiteGraph 4 2` on `Fin 4 × Fin 2`), box(G) = 4 while box(Ḡ) ≤ 1 (the complement is the perfect matching 4K₂, represented by disjoint intervals [3i, 3i+1]), so the gap is ≥ 3 > 2. The lower bound box(G) ≥ 4 is Roberts' argument, fully formal: each non-adjacent pair {(i,0), (i,1)} needs a separating coordinate; the general `interval_lemma` (two closed intervals that each meet both sides of a disjoint pair must meet each other — pure linarith) shows no coordinate can separate two different pairs; pigeonhole (`Fintype.exists_ne_map_eq_of_card_lt`) contradicts d < 4. A 4-dimensional representation is also given. Lean: `BoxRep`, `boxicity`, `repCompl`, `repK`, `interval_lemma`, `no_rep_of_lt_four`, `boxicity_K`, `conjecture_00000003965_false : ¬ BoxicityGapAtMostTwo`.

## Verification notes
`lake build` exit 0; axiom audit clean. `BoxRep` is the genuine object (real endpoints l ≤ r per coordinate, adjacency iff overlap in every coordinate, boxicity = sInf), and the claim quantifies over all finite graphs. The upper-bound representations and the interval lemma were checked; the math matches Roberts (1969): boxicity of a complete k-partite graph with all parts of size ≥ 2 is k, and the complement of K_{2,2,2,2} is 4K₂ with boxicity 1. The "difference 2 attained" clause cannot rescue the conjecture, which is a conjunction whose first clause is false. LaTeX consistent; PDF present.

## Verdict
APPROVED — merged into main.
