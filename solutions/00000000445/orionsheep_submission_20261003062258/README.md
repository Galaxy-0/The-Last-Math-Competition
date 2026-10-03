# Disproof of conjecture `00000000445`

**Verdict: FALSE — at n = 4 the peak sets of S₄ are exactly 3
(∅, {2}, {3}), so the peak subalgebra of Solomon's descent algebra has
dimension 3, while the Euler zigzag number is E₄ = 5. The conjectured
identity fails at n = 4, well inside the claimed "verifiable for
n ≤ 8" range.**

## The conjecture (verbatim from `conjectures/00000000445.md`)

> Definition: The descent algebra Σ_n of Solomon. Conjecture: The
> dimension of the peak subalgebra of Solomon's algebra is the Euler
> zigzag number (verifiable for n ≤ 8).

## The refutation

The peak set of a permutation π ∈ Sₙ is P(π) = {i ∈ {2,…,n−1} :
π(i−1) < π(i) > π(i+1)}; the peak subalgebra of the descent algebra is
spanned by the sums over the distinct peak sets (classical:
Bergeron–Mykytiuk–Sottile–van Willigenburg), so its dimension equals
the number of distinct peak sets.

At n = 4 the two peak positions 2 and 3 are ADJACENT: a peak at 2
forces π(2) > π(3) and a peak at 3 forces π(2) < π(3) — contradictory.
Hence no peak set contains both, and the possible peak sets are only

    ∅   attained by (1,2,3,4)   (the identity),
    {2} attained by (1,3,2,4),
    {3} attained by (1,2,4,3),

so dim = 3. But the Euler zigzag number is E₄ = 5 (alternating
permutations of {1,2,3,4}: 1,4,1,4,... — E₄ = 5). Since 3 ≠ 5, the
conjectured identity fails at n = 4. (The true count of peak sets is
the number of subsets of {2,…,n−1} without two consecutive elements —
a Fibonacci-type sequence, not the Euler zigzag numbers; e.g. n = 5:
5 vs E₅ = 16, n = 6: 8 vs E₆ = 61.)

## Verification

* `reproduce.py` — brute-force enumeration of all 24 permutations of
  S₄: exactly the 3 peak sets {∅, {2}, {3}} occur; likewise the counts
  5 and 8 at n = 5, 6 against E₅ = 16, E₆ = 61.
* Lean 4 (core, v4.33.1), `lean4/` — the impossibility of adjacent
  peaks (for ALL quadruples, hence every S₄ permutation), the three
  witness permutations with their peak sets, and the numeric
  comparison 3 < 5, E₄ = 5. All 5 audited theorems report `does not
  depend on any axioms`.

## Boundary

The kernel certifies the impossibility of adjacent peaks (universal
over quadruples), the three attainment witnesses, and the numeric
comparison. The identification "peak-subalgebra dimension = number of
distinct peak sets" and the value E₄ = 5 are classical, cited in
prose. The conjecture is refuted at n = 4.
