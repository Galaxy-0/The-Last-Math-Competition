# Solution Review — Conjecture 00000007965 (PR 320)

**Submission:** feiyuceng06-prog — `feiyuceng06-prog_submission_20261003083436`
**Reviewer:** competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-03

## Checklist
- [x] LaTeX source and PDF present
- [x] Lean 4 project compiles completely (lake build, exit 0, cold cache)
- [x] No `sorry`, no `native_decide`, no extra axioms (`#print axioms` exactly `[propext, Classical.choice, Quot.sound]`)
- [x] Submission matches the conjecture's objects and literal statement

## Conjecture (verbatim summary)
Isospectral classes of linear codes under the MacWilliams/Krawtchouk transform. Clause 2: the minimal example of isospectral but non-permutation-equivalent codes is the unique pair at (n,k) = (9,4).

## What the submission proves
Two binary [6,3] codes — row spaces of G_A = [111001; 000101; 000011] and G_B = [110000; 001100; 000011] — have the same weight enumerator 1 + 3z² + 3z⁴ + z⁶ but are not permutation equivalent (A's weight-2 words pairwise share a coordinate; B's are pairwise disjoint; both properties are permutation invariants). Since (6,3) < (9,4) under every natural order, minimality fails. Two distinct inequivalent isospectral pairs at (9,4) — direct sums with ⟨111⟩ and with ⟨100⟩ — are also formalized, so uniqueness fails. Lean: `¬ MinimalAtNineFour`, `¬ UniqueAtNineFour`, `conjecture_00000007965_false : ¬ (MinimalAtNineFour ∧ UniqueAtNineFour)` (plus a primed version `¬ (P ∧ Clause2 ∧ Q)` covering any reading of the other two clauses).

## Verification notes
Cold-cache `lake exe cache get!` + `lake build` exit 0 (Mathlib v4.33.1 pinned). All 7 audited theorems report exactly the three standard axioms. The two invariants (`weightDist_eq_of_permEquiv`, `not_permEquiv_of_disjoint`) are genuine general proofs; finite facts (encoder injectivity, weight distributions, weight-2 supports) are `decide`-checked over the actual row spaces. Aux `search.py` runs in ~13 s and confirms: no example at n ≤ 5, and a unique isospectral-inequivalent group at (6,3) — the submitted pair up to coordinate permutation. Reviewer independently re-verified by brute force: enumerating all 720 permutations of S₆ (no permutation maps A to B) and all 362,880 of S₉ (none equates the two (9,4) pairs); weight enumerators recomputed from the 8 codewords of each code. LaTeX consistent with the Lean and the search output. Binary codes are in scope (the conjecture's own claimed pair at (9,4) is binary, and monomial = permutation equivalence for binary linear codes).

## Verdict
APPROVED — merged into main (PR 320, merge commit 9945d9ca).
