#!/usr/bin/env python3
"""Standalone recomputation for the disproof of TLMC conjecture 00000000156.

Claim being refuted: "the probability that |det| of a random +-1 n x n matrix is
prime is ~ c/n".

This script verifies, with no third-party dependencies:
  1. For every +-1 n x n matrix, n <= 4 exhaustively, 2^(n-1) | det.
  2. For n >= 3 no |det| is prime (exhaustive n = 3, 4; random n = 5..8).
  3. n = 2: exactly 8 of 16 matrices give the prime |det| = 2 (probability 1/2).
"""

from itertools import product
import random


def det_bareiss(M):
    """Exact integer determinant via the Bareiss (fraction-free) algorithm."""
    n = len(M)
    M = [row[:] for row in M]
    sign, prev = 1, 1
    for k in range(n - 1):
        if M[k][k] == 0:
            for i in range(k + 1, n):
                if M[i][k] != 0:
                    M[k], M[i] = M[i], M[k]
                    sign = -sign
                    break
            else:
                return 0
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                M[i][j] = (M[i][j] * M[k][k] - M[i][k] * M[k][j]) // prev
        prev = M[k][k]
    return sign * M[n - 1][n - 1]


def is_prime(m):
    if m < 2:
        return False
    if m < 4:
        return True
    if m % 2 == 0:
        return False
    d = 3
    while d * d <= m:
        if m % d == 0:
            return False
        d += 2
    return True


def main():
    ok = True

    # Exhaustive n = 1..4
    for n in range(1, 5):
        total = div_ok = primes = 0
        detset = set()
        for entries in product((-1, 1), repeat=n * n):
            M = [list(entries[i * n:(i + 1) * n]) for i in range(n)]
            d = det_bareiss(M)
            total += 1
            div_ok += d % (2 ** (n - 1)) == 0
            primes += is_prime(abs(d))
            detset.add(d)
        print(f"n={n}: total={total}  det % 2^(n-1)==0: {div_ok}/{total}  "
              f"prime |det|: {primes}  det values: {sorted(detset)}")
        ok &= div_ok == total
        ok &= (primes == 8) if n == 2 else (primes == 0)

    # Randomized n = 5..8
    random.seed(156)
    for n in range(5, 9):
        N, div_ok, primes = 3000, 0, 0
        for _ in range(N):
            M = [[random.choice((-1, 1)) for _ in range(n)] for _ in range(n)]
            d = det_bareiss(M)
            div_ok += d % (2 ** (n - 1)) == 0
            primes += is_prime(abs(d))
        print(f"n={n}: random {N} samples  det % 2^(n-1)==0: {div_ok}/{N}  "
              f"prime |det|: {primes}")
        ok &= div_ok == N and primes == 0

    print("RESULT:", "ALL CHECKS PASS — det always divisible by 2^(n-1); "
          "prime |det| occurs only at n=2 (8/16); conjecture ~ c/n is FALSE"
          if ok else "FAILED")


if __name__ == "__main__":
    main()
