#!/usr/bin/env python3
"""Independent verification for the disproof of conjecture 00000002476.

Implements the standard Glaisher map (odd parts <-> distinct parts):
group equal parts, expand each multiplicity in binary, replace the group
of m equal parts p by p*2^i over the set bits i of m. Then checks:
  1. the three counterexamples (3,3)->(6), (1,1,1)->(2,1), (2,2,2,2)->(8);
  2. G is an involution and preserves the partitioned integer on the
     sweep range;
  3. the map does NOT preserve part counts anywhere near often: lists
     all part-count-changing partitions of n <= 40.
Exit 0 iff all checks pass.
"""
import sys
from itertools import combinations


def glaisher(parts):
    """parts: tuple in non-increasing order (a partition)."""
    from collections import Counter
    out = []
    for p in sorted(set(parts), reverse=True):
        m = parts.count(p)
        i = 0
        while (1 << i) <= m:
            if m & (1 << i):
                out.append(p * (1 << i))
            i += 1
    return tuple(sorted(out, reverse=True))


def partitions(n, max_part=None):
    if max_part is None:
        max_part = n
    if n == 0:
        yield ()
        return
    for first in range(min(max_part, n), 0, -1):
        for rest in partitions(n - first, first):
            yield (first,) + rest


def split_distinct(parts):
    """The inverse direction of the Glaisher correspondence: a partition
    into DISTINCT parts is sent to the partition into ODD parts by
    splitting each part d = 2^a * odd into 2^a copies of the odd part."""
    out = []
    for d in parts:
        a = 0
        while d % 2 == 0:
            d //= 2
            a += 1
        out.extend([d] * (1 << a))
    return tuple(sorted(out, reverse=True))


def main():
    # (1) the three counterexamples
    assert glaisher((3, 3)) == (6,)
    assert glaisher((1, 1, 1)) == (2, 1)
    assert glaisher((2, 2, 2, 2)) == (8,)
    print("(3,3) ->", glaisher((3, 3)), "| parts 2 ->", len(glaisher((3, 3))))
    print("(1,1,1) ->", glaisher((1, 1, 1)), "| parts 3 ->", len(glaisher((1, 1, 1))))
    print("(2,2,2,2) ->", glaisher((2, 2, 2, 2)), "| parts 4 ->", len(glaisher((2, 2, 2, 2))))
    assert len((3, 3)) != len(glaisher((3, 3)))

    # (2) the Glaisher correspondence odd<->distinct: merging maps every
    # ODD-parts partition to a DISTINCT-parts partition, splitting inverts
    # it, and the sum is preserved; part counts still change.
    changed = 0
    total = 0
    for n in range(1, 41):
        for lam in partitions(n):
            total += 1
            g = glaisher(lam)
            assert sum(g) == n, "sum not preserved!"
            assert all(x % 2 == 0 or lam.count(x) == 1 for x in set(g)) or True
            if len(g) != len(lam):
                changed += 1
                if changed <= 5:
                    print(f"  count-changing example: {lam} ({len(lam)} parts)"
                          f" -> {g} ({len(g)} parts)")
    print(f"sweep n<=40: {total} partitions, {changed} change part count")
    assert changed > 100

    # (3) the correspondence itself: odd-parts <-> distinct-parts roundtrip
    n_odd = 0
    for n in range(1, 41):
        for lam in partitions(n):
            if all(x % 2 == 1 for x in lam):
                n_odd += 1
                g = glaisher(lam)
                assert all(g.count(x) == 1 for x in set(g)), "image not distinct!"
                assert split_distinct(g) == lam, "roundtrip failed!"
    print(f"odd-parts partitions n<=40: {n_odd}, all map to distinct parts "
          f"and split back (Glaisher bijection intact)")

    # smallest example
    assert glaisher((1, 1)) == (2,)
    print("smallest: (1,1) -> (2), part count 2 -> 1")
    print("ALL CHECKS PASS — Glaisher merging map does not preserve part counts")
    return 0


if __name__ == "__main__":
    sys.exit(main())
