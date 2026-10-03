# Disproof of conjecture `00000002037`

**Verdict: FALSE — a 50-tuple with all pair gaps ≤ 16 would need 50
distinct integers inside a window of diameter 16, which holds only 17
slots: 49 ≤ 16 is absurd. No such tuple exists, admissible or not.**

## The conjecture (verbatim from `conjectures/00000002037.md`)

> Definition: An admissible tuple is an integer tuple with no fixed
> prime divisor. Conjecture: There exists an explicit admissible
> 50-tuple for which DHL[50,2] holds (giving infinitely many prime pairs
> with gap ≤ 16); the tuple is centered near 7·11·13.

## The refutation

DHL[50,2] with gap bound 16 means: infinitely many n such that n + t and
n + t′ are both prime for two elements t, t′ of the tuple — so two
tuple elements differ by at most 16. For the derived pairs to have gap
≤ 16, the tuple's diameter (max element − min element) must be ≤ 16
(otherwise pairs beyond that span are never formed — the standard
reading of a prime-pair-producing k-tuple).

But a tuple of 50 DISTINCT integers with diameter ≤ 16 lives in
{a, a+1, …, a+16} — 17 slots for 50 elements. In the canonical
increasing presentation t(0) < t(1) < ⋯ < t(49):

    t(k) ≥ t(0) + k  (each step gains at least 1),

so t(49) ≥ t(0) + 49 ≥ a + 49 > a + 16 — contradiction, kernel-certified
uniformly in the center a. No admissibility analysis is even needed:
arithmetic capacity fails first.

(The claim is also internally inconsistent on the "centering": 7·11·13
= 1001, and 50 elements within ±16 of 1001 requires 50 of the 33 slots
{985,…,1017}.)

## Verification

* `reproduce.py` — brute-force check: counts the maximum size of a
  strictly increasing integer sequence within a window of diameter 16
  (exactly 17), for every window start a in a wide range; and verifies
  that any 50 distinct integers have diameter ≥ 49.
* Lean 4 (core, v4.33.1) — `lean4/`: the step-growth lemma
  (t(i+k) ≥ t(i) + k for strictly increasing t), the window
  contradiction a+49 ≤ a+16 → False, and the refutation of existence.
  All 4 audited theorems report `does not depend on any axioms`.

## Boundary

Only the "gap ≤ 16 with a 50-tuple" clause is refuted (it fails for any
50-tuple over the integers). DHL[k,2] itself, admissibility theory, and
larger gap bounds are not addressed.
