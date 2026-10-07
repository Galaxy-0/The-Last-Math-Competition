# Solution Review — Conjecture 00000002291 (PR 716)

**Submission:** Jackmeson1 — `Jackmeson1_submission_20261005140903`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

## Checklist results
- Official conjecture read (EN+CN): Brauer–Fowler context; claim |C_G(x)| ≥ c·|G|^{1/2} with c = 1/8 for centralizers in even-order simple groups; c tight, attained by low-order simple groups (e.g. involutions of A₅). `conjecture.md` byte-identical to the official file.
- LaTeX: independent rebuild exits 0 (4 pages); content matches; extraction artifacts only.
- Lean build: exit 0, 8708 jobs, zero errors/warnings.
- Forbidden content: none.
- Axioms: my independent `CheckJ6.lean` over all 26 theorems: exactly `[propext, Classical.choice, Quot.sound]`.
- Auxiliary code: only verification logs shipped; I re-ran the numbers the tex attributes to an "attached Python" (which is not in the package): centralizer orders in A₅ are 3, 4, 5, 60 and all 15 involutions have |C| = 4, ratio 4/√60 ≈ 0.516 — confirmed.
- Sanity check: 9 < (1/8)·425.96 ≈ 53.2; 128 < (1/8)·√2097024 ≈ 181.0; (1/8)√60 ≈ 0.968 < 1 — all confirmed.

## Semantic audit
Since the conjecture never says which x the bound covers, the submission formalizes and refutes BOTH natural readings, each by its exact negation, and in each case also proves the stronger statement that no positive constant works — so no re-reading of the constant can rescue the claim.

Reading R1 (every nonidentity x): `LowerBoundAllElements` (finite, simple, nonabelian, even order; x ≠ 1). Refuted in A₉: `card_centralizer_finRotate_perm` computes |C_{S₉}(9-cycle)| = 9 from Mathlib's cycle-type formula, `card_centralizer_cyc_le` injects the A₉-centralizer into it, and `ratio_aux` (q² r ≤ N, C ≤ q, c² r > 1 ⟹ C < c√N) with r = 2240 gives |C| < (1/8)√181440. `alternating_centralizer_ratio_small` shows no c > 0 works (n-cycle in A_{2m+1}, m = ⌈1/c²⌉+2, using n! ≥ n²(n−3)). The nonabelianness and simplicity hypotheses are proved where needed (simplicity from Mathlib for n ≥ 5; abelian case excluded via the centralizer becoming everything).

Reading R2 (involutions): `LowerBoundInvolutions`, refuted in PSL(2, 𝔽₁₂₈). The Lean development proves in characteristic 2 that Z(SL(2,F)) is trivial (scalar rI with r² = 1 forces r = 1), so SL ≅ PSL; the transvection T = [[1,1],[0,1]] satisfies T² = 1 ≠ T; commutation with T forces [[1,b],[0,1]]; hence |C(t)| ≤ q; and |SL| ≥ (q−1)q² by an explicit injection Fˣ×F×F → SL. With q = 128: |C(t)| ≤ 128 < (1/8)√|G| ≈ 181. `psl_centralizer_ratio_small` kills every c > 0 using PSL(2, 2^k). Simplicity is Mathlib's `rank_two_simple` for |F| ≥ 4. This is all correct linear algebra, independently verified numerically.

Tightness clause: `not_attainedByA5Involution` — (1/8)√60 < 1 ≤ |C(x)| for every x ∈ A₅ (the named attainment is impossible since the conjectured value is smaller than every centralizer order), and `a5_not_near_tight` — every nonidentity x has |C(x)| ≥ 2 > 2·(1/8)√60. Both exact negations. Adding the nonabelian hypothesis to the formal readings only weakens them, and both witnesses satisfy it.

## Issues found
- Minor: proof.tex says the A₅ centralizer table was "checked by brute force in the attached Python", but no Python file is shipped in the package. Non-blocking: the claim is correct, is not used by the Lean proof, and I verified it independently.
- `verification/SHA256SUMS.txt`: two CRLF artifacts (content verified identical). Cosmetic.

## Verdict
APPROVED. Both readings of the lower bound are false (A₉ and PSL(2,128) witnesses, with no positive constant working under either reading), and the named attainment at A₅ is impossible; the formalization proves the objects (simplicity, centralizer orders, involution structure) rather than numerals, the build is clean, and the axioms are exactly the standard three.
