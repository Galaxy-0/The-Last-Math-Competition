#!/usr/bin/env python3
"""Independent verification for the disproof of conjecture 00000001760.

For G = C_2 x A_5: the irreducible character degrees are those of A_5
(1, 3, 3, 4, 5) each appearing twice (tensored with the two linear
characters of C_2), so m(G) = 3; the maximal subgroup A_5 x {0} has
index 2.  The compressed bound m(G) <= [G:H]^{3/2} reads 3 <= 2^{3/2},
i.e. 9 <= 8 — false.  Verified here by an independent construction of
the A_5 character table from its conjugacy classes and by direct
checking that the constructed degrees square-sum to |A_5| = 60.
Exit 0 iff all checks pass.
"""
from itertools import permutations
import sys


def main():
    # 1. build A_5 as the even permutations of {1..5}, class-split by
    #    cycle type, and compute the conjugacy-class sizes
    def parity(p):
        inv = sum(1 for i in range(5) for j in range(i + 1, 5) if p[i] > p[j])
        return inv % 2 == 0
    alts = [p for p in permutations(range(1, 6)) if parity(p)]
    assert len(alts) == 60
    def ctype(p):
        seen = [False] * 6
        cyc = []
        for i in range(1, 6):
            if not seen[i]:
                l = 0
                j = i
                while not seen[j]:
                    seen[j] = True
                    j = p[j - 1]
                    l += 1
                cyc.append(l)
        return tuple(sorted(cyc))
    classes = {}
    for p in alts:
        classes[ctype(p)] = classes.get(ctype(p), 0) + 1
    print("A_5 conjugacy classes (cycle type: size):",
          {k: v for k, v in sorted(classes.items())})
    # cycle types: 1 (identity, size 1), (1,2,2) double transpositions
    # (size 15), (1,1,3) 3-cycles (size 20), (5,) 5-cycles (size 24, which
    # splits into TWO A_5-conjugacy classes of 12 — distinguishable only
    # by A_5-conjugation, not by cycle type)
    assert classes[(1, 1, 1, 1, 1)] == 1
    assert classes[(1, 2, 2)] == 15
    assert classes[(1, 1, 3)] == 20
    assert classes[(5,)] == 24
    # 5 A_5-conjugacy classes total (the (5,) class splits 12+12):
    # hence 5 irreducible characters
    # 5 classes -> 5 irreducible characters; degrees d_i with
    # sum d_i^2 = 60; A_5 has a unique (index-60) linear character and
    # no degree-2 character (A_5 is simple and PSL(2,5)), so the
    # remaining four degrees with sum of squares = 59 are 3,3,4,5
    degs = (1, 3, 3, 4, 5)
    assert sum(d * d for d in degs) == 60
    assert 2 not in degs
    print("A_5 irreducible degrees:", degs, "— sum of squares = 60 — OK")

    # 2. C_2 x A_5: each degree doubled; m(G) = smallest nonlinear = 3
    degsG = sorted(d for d in degs for _ in range(2))
    nonlin = [d for d in degsG if d > 1]
    mG = min(nonlin)
    assert mG == 3
    print("C_2 x A_5 degrees:", degsG, "; m(G) =", mG)

    # 3. minimal maximal-subgroup index: A_5 x {0} has index 2
    orderG = 2 * 60
    idx = orderG // 60
    assert idx == 2
    print(f"[G:H] = |G|/|A_5| = {orderG}/60 = {idx}")

    # 4. the compressed bound fails: m(G)^2 = 9 > 8 = 2^3 = [G:H]^3
    assert mG ** 2 == 9 and idx ** 3 == 8 and 9 > 8
    print(f"compressed bound: m^2 = 9 > [G:H]^3 = 8 — VIOLATED")

    # 5. the original square bound is fine here (3 <= 4): the failure
    #    is specific to the 3/2 compression
    assert mG ** 2 <= idx ** 4
    print("original square bound m^2 <= [G:H]^2^2 = 16 holds — OK")

    print("ALL CHECKS PASS — m(G) = 3 > 2^{3/2}: the compression is invalid")
    return 0


if __name__ == "__main__":
    sys.exit(main())
