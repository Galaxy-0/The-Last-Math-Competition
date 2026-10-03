#!/usr/bin/env python3
"""Independent verification for the disproof of conjecture 00000001681.

In a rainbow-triangle-free coloring of K_n the number of rainbow C4s is
identically 0 (a rainbow C4 forces a rainbow triangle on its four
vertices), while (1/24)*n^2 > 0 for every n >= 1: the claimed lower
bound fails on the entire class.
Exit 0 iff all checks pass.
"""
import itertools
import sys
from fractions import Fraction
from itertools import combinations, product


def main():
    # 1. pigeonhole: no 3- or 4-tuple of Bool values is pairwise distinct
    for k in (3, 4):
        for tup in product((False, True), repeat=k):
            assert len(set(tup)) < k, f"pairwise-distinct {tup}?!"
    print("pigeonhole: no 3- or 4-tuple of Bool is pairwise distinct — OK")

    # 2. the constant 2-coloring: symmetric, no rainbow triangle, and no
    #    rainbow C4 on any four distinct vertices
    def col(a, b):
        return False  # the constant 2-coloring

    for n in range(3, 10):
        for verts in combinations(range(n), 3):
            v1, v2, v3 = verts
            tri = [col(v1, v2), col(v2, v3), col(v1, v3)]
            assert len(set(tri)) != 3, "found a rainbow triangle?!"
    for n in range(4, 10):
        for verts in combinations(range(n), 4):
            v1, v2, v3, v4 = verts
            cyc = [col(v1, v2), col(v2, v3), col(v3, v4), col(v4, v1)]
            assert len(set(cyc)) != 4, "found a rainbow C4?!"
    print("constant 2-coloring of K_3..K_9: member of the class, zero "
          "rainbow C4s — OK")

    # 3. structural fact: in ANY complete-graph coloring, a rainbow C4
    #    (cycle edges pairwise distinct) forces a rainbow triangle —
    #    exhaust all such K4 colorings (diagonals arbitrary)
    checked = 0
    for perm in itertools.permutations((0, 1, 2, 3)):
        a, b, c, d = perm  # cycle edges 12, 23, 34, 41
        for x in range(6):        # diagonal 13
            for y in range(6):    # diagonal 24
                tris = ({a, b, x},   # 123
                        {b, c, y},   # 234
                        {c, d, x},   # 134
                        {d, a, y})   # 124
                assert any(len(t) == 3 for t in tris), \
                    "rainbow C4 without a rainbow triangle?!"
                checked += 1
    print(f"structural check: all {checked} rainbow-C4 K4 colorings "
          "force a rainbow triangle — OK")

    # 4. the claimed bound is positive for every n >= 1
    for n in range(1, 200):
        assert Fraction(n * n, 24) > 0
    assert Fraction(0) < Fraction(1, 24)
    print("(1/24)*n^2 > 0 for all 1 <= n < 200; 24*0 < n*n — OK")

    print("ALL CHECKS PASS — the class's rainbow-C4 count is 0, and "
          "0 < (1/24)*n^2 for every n >= 1")
    return 0


if __name__ == "__main__":
    sys.exit(main())
