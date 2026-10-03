#!/usr/bin/env python3
"""Independent verification for the disproof of conjecture 00000000445.

Peak sets of S_n: subsets of {2..n-1} realizable as {i : pi(i-1) < pi(i)
> pi(i+1)}. At n = 4 exactly 3 occur vs the Euler zigzag number E4 = 5.
Exit 0 iff all checks pass.
"""
from itertools import permutations
import sys


def peak_set(p):
    return frozenset(i + 1 for i in range(1, len(p) - 1)
                     if p[i - 1] < p[i] > p[i + 1])


def euler_zigzag(n):
    """Euler zigzag (up-down) numbers, OEIS A000111, classical values."""
    A = [1, 1, 1, 2, 5, 16, 61, 272, 1385]
    return A[n]


def main():
    counts = {}
    for n in (4, 5, 6, 7, 8):
        psets = {peak_set(p) for p in permutations(range(1, n + 1))}
        counts[n] = len(psets)
        E = euler_zigzag(n)
        print(f"n = {n}: {len(psets)} peak sets {sorted(sorted(s) for s in psets)}"
              f" vs E_{n} = {E}")
        assert len(psets) != E, f"unexpected agreement at n = {n}"
    assert counts[4] == 3
    assert counts[5] == 5
    assert counts[6] == 8
    assert euler_zigzag(4) == 5
    # witnesses in S_4
    assert peak_set((1, 2, 3, 4)) == frozenset()
    assert peak_set((1, 3, 2, 4)) == frozenset({2})
    assert peak_set((1, 2, 4, 3)) == frozenset({3})
    print("witnesses (1,2,3,4), (1,3,2,4), (1,2,4,3) give {}, {2}, {3} — OK")
    print("ALL CHECKS PASS — dim(peak_4) = 3 != E_4 = 5")
    return 0


if __name__ == "__main__":
    sys.exit(main())
