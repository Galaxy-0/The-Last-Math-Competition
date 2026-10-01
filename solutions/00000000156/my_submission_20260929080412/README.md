# Disproof of Conjecture 00000000156

**Verdict: FALSE.**

**Conjecture (recalled).** The probability that the determinant of a random ±1 n×n matrix
is prime in absolute value is ~ c/n (with an explicit formula for c).

## Attack

For every n×n matrix A with all entries ±1, the determinant is divisible by 2^(n-1):
subtract the first row from each of rows 2..n (a determinant-preserving row operation);
rows 2..n then have all entries in {0, -2}; factoring 2 out of each of those n-1 rows gives
det A = 2^(n-1) · det B with B an integer matrix.

Consequently, for n ≥ 3 we have 4 | det A. Since |det A| is even and (when nonzero) at
least 4, it can never be prime — the only even prime is 2, and 4 ∤ 2. Hence

P(|det| prime) = 0 exactly, for every n ≥ 3,

whereas ~ c/n with the conjectured positive constant c would require probability c/n → 0
along a positive multiple of 1/n (ratio → 1). The actual probability is identically 0, so
the asymptotic ~ c/n fails for every c > 0. The conjecture is false.

## Boundary (small n, exact)

* n = 1: det ∈ {−1, 1}; |det| never prime. P = 0.
* n = 2: det = ad − bc ∈ {−2, 0, 2}; |det| = 2 is prime. P = 8/16 = 1/2.
  (This is the only case where a prime determinant can occur; matching c/2 = 1/2
  would force c = 1, but then c/n = 1/n ≠ 0 = P for all n ≥ 3.)
* n = 3: exhaustive over all 2^9 = 512 matrices: det ∈ {−4, 0, 4}, all divisible by 4,
  zero primes.
* n = 4: exhaustive over all 2^16 = 65536 matrices: det ∈ {0, ±8, ±16}, all divisible
  by 8, zero primes.
* n = 5..8: 3000 random samples each (reproduce.py, seed 156): 100% divisible by
  2^(n−1), zero primes.

## Contents

* `main.tex`, `build/main.pdf` — full write-up (proof of the 2^(n−1) divisibility, the
  disproof, exact small-n boundary).
* `reproduce.py` — standalone recomputation (no third-party dependencies): exhaustive
  enumeration for n ≤ 4 and randomized checks for n = 5..8.
* `lean4/` — core-Lean (no Mathlib) formalization: zero axioms, zero `sorry`.
  - general arithmetic core: a number `m = 2 * (2 * q)` (i.e. `4 | m`) cannot
    be prime (`no_prime_det`); with the hand-proved `2^(n-1) | det A` this gives
    probability exactly 0 for all n ≥ 3 (`no_prime_det`), and `n = 2` is the
    lone feasible case (`two_is_possible`);
  - exhaustive `decide` verification over the 16 determinants of all ±1 2×2
    matrices and the 512 determinants of all ±1 3×3 matrices (bit enumeration,
    matching reproduce.py): divisibility by 2^(n−1), absence of prime |det|, and
    the count 8 of prime determinants at n = 2.

## Reproduce

```
python3 reproduce.py
cd lean4 && lake build && lake env lean Check.lean
```
