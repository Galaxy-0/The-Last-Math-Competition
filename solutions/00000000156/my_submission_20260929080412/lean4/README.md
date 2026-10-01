# Lean 4 verification (core Lean, no Mathlib)

Disproof of TLMC conjecture 00000000156 ("the probability that |det| of a random
±1 n×n matrix is prime is ~ c/n").

## Build and audit

```
lake build
lake env lean Check.lean
```

Every theorem in `Check.lean` must report `does not depend on any axioms`.
The development uses **zero axioms and zero `sorry`**.

## What is proved

* `no_prime_det` — the arithmetic heart: if `4 | m` (written `m = 2 * (2 * q)`)
  then `m` is not prime. Combined with the classical fact `2^(n-1) | det A` for
  ±1 matrices (row reduction, proved in `../main.tex`), which for `n ≥ 3`
  implies `4 | |det A|`, this yields probability exactly 0 for all `n ≥ 3`,
  refuting the `~ c/n` asymptotic.
* `two_is_possible` — `n = 2`, `m = 2` is prime and even: the lone feasible case.
* `all_dvd_2`, `count_prime_2` — exhaustive `decide` over the 16 determinants of
  all ±1 2×2 matrices (bit enumeration): all divisible by 2, exactly 8 prime
  (probability 1/2).
* `all_dvd_4`, `no_prime_3` — exhaustive `decide` over the 512 determinants of
  all ±1 3×3 matrices: all divisible by 4 (values in {0, ±4}), none prime.

`reproduce.py` regenerates both determinant lists and re-verifies everything
exhaustively for n ≤ 4 and randomly for n = 5..8.

Toolchain: `leanprover/lean4:v4.33.1`.
