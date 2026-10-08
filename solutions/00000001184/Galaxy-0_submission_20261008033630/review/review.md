# Solution Review — Conjecture 00000001184 (PR 845)

**Submission:** Galaxy-0 — `Galaxy-0_submission_20261008033630`
**Reviewer:** independent competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-08

## Checklist results
- Conjecture read: yes — the source asserts that for finite Lie-type groups the pair-generation (Dixon) probability is bounded below by `1 − 1/q − 1/q²`, and that this bound is asymptotically tight for large `q`.
- Change scope: only `solutions/00000001184/Galaxy-0_submission_20261008033630/` was added; the conjecture is unsolved in the base metadata.
- LaTeX: `proof.tex` read in full. The disproof is a finite certificate and is complete.
- Lean build: Lean 4.31.0, standard-library-only project. `lake build` exit 0; project sets `warningAsError` and builds cleanly. The final `#print axioms` shows only `[propext, Classical.choice, Quot.sound]`.
- Forbidden content: none.
- Auxiliary code: `check_independent.py` re-run independently — reconstructs the group from residue matrices and re-verifies the subgroup certificates and the common missing witness `(0,1,4,3)`.

## Semantic audit
Take `G = PSL₂(F₅) = SL₂(F₅)/{±I}`, a finite group of Lie type `A₁` with `q = 5`. The submission proves `|G| = 60` by an explicit enumeration (`enumeration_correct`, `group_order`), with a verified model of the quotient-group multiplication (`mul_assoc`, `matrix_group_axioms`, `normalize_fibers`, `normalize_product`). It then exhibits eight proper subgroups (sizes `12,12,12,12,12,10,10,10`), each kernel-checked to contain the identity, be closed under multiplication and inversion, and to omit the witness `w = (0,1,4,3)`. Any pair lying in a single `H_i` cannot generate `G`, so at most `3600 − 888 = 2712` ordered pairs generate; hence the generation probability is at most `2712/3600 = 113/150 < 19/25 = 1 − 1/5 − 1/25`.

The Lean theorem `conjecture1184_false` proves `¬ ClaimedDixonBoundAtFive`, where `ClaimedDixonBoundAtFive` is `19·|G|² ≤ 25·generatingCount`, i.e. exactly the cross-multiplied form of the conjectured lower bound at `q = 5`. The bound `generatingCount ≤ 2712` is derived via `generating_count_bound` from the subgroup certificates (a finite-list monotonicity lemma). The value `2712` is a proven upper bound, which suffices to refute the lower bound; no exact generating-pair count is needed.

## Issues found
- The submission refutes the universal lower-bound clause at `q = 5`; it does not address the separate large-`q` tightness clause, which is not needed to disprove the conjunction.

## Verdict rationale
The counterexample is exact and kernel-checked: `PSL₂(F₅)` is a genuine finite Lie-type group with `q = 5`, and its pair-generation probability is strictly below the conjectured bound. The Lean project compiles with only the three standard axioms and contains no forbidden content.

## Disposition
APPROVED — ready to merge (PR 845).
