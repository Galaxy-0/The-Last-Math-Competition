#!/usr/bin/env python3
"""Standalone recomputation for the disproof of conjecture 00000000423.

Enumerates SYT of a given shape by brute force, computes Schutzenberger
promotion (delete 1, jeu-de-taquin slide, subtract 1, place n), and prints the
promotion orbits. No third-party dependencies.
"""
from itertools import permutations


def shape_cells(shape):
    """Cells (row, col), 0-indexed, of a partition shape (row lengths)."""
    return [(r, c) for r, row in enumerate(shape) for c in range(row)]


def enum_syt(shape):
    """All standard Young tableaux of `shape`, as dicts cell -> entry."""
    cells = shape_cells(shape)
    n = len(cells)
    out = []
    for perm in permutations(range(1, n + 1)):
        t = dict(zip(cells, perm))
        if all(t[(r, c)] < t.get((r, c + 1), 99) and
               t[(r, c)] < t.get((r + 1, c), 99) for (r, c) in cells):
            out.append(t)
    return out


def promotion(t, n):
    """Schutzenberger promotion on a tableau with n cells."""
    u = dict(t)
    del u[(0, 0)]                      # delete the entry 1 at cell (1,1)
    empty = (0, 0)
    while True:                        # jeu-de-taquin slide
        r, c = empty
        nbrs = [u[p] for p in ((r, c + 1), (r + 1, c)) if p in u]
        if not nbrs:
            break
        v = min(nbrs)
        for p in ((r, c + 1), (r + 1, c)):
            if u.get(p) == v:
                del u[p]
                u[empty] = v
                empty = p
                break
    u = {k: v - 1 for k, v in u.items()}   # subtract 1 everywhere
    u[empty] = n                           # place n in the vacated corner
    return u


def orbits(syts):
    seen, out = set(), []
    for t in syts:
        k = tuple(sorted(t.items()))
        if k in seen:
            continue
        orb, cur = [t], t
        while True:
            cur = promotion(cur, len(t))
            if tuple(sorted(cur.items())) == k:
                break
            orb.append(cur)
            seen.add(tuple(sorted(cur.items())))
        out.append(orb)
    return out


def fmt(t, shape):
    return [[t.get((r, c)) for c in range(shape[r])] for r in range(len(shape))]


def main():
    # ---- Attack: shape (2,1), n = 3 cells -------------------------------
    shape = (2, 1)
    syts = enum_syt(shape)
    n = sum(shape)
    orbs = orbits(syts)
    lens = sorted(len(o) for o in orbs)
    print(f"shape (2,1): n(cells)={n}, #SYT={len(syts)}")
    for o in orbs:
        print("  orbit:", [fmt(t, shape) for t in o], "length", len(o))
    assert len(syts) == 2, "SYT(2,1) should number exactly 2"
    assert lens == [2], f"promotion orbits on SYT(2,1) should be [2], got {lens}"
    assert n % 2 != 0, "2 should NOT divide n = 3"
    print("  => single orbit of length 2; 2 does not divide n = 3. CONJECTURE FALSE\n")

    # ---- Boundary: shape (3,2), n = 5 cells, #SYT = 5 -------------------
    shape = (3, 2)
    syts = enum_syt(shape)
    n = sum(shape)
    orbs = orbits(syts)
    lens = sorted(len(o) for o in orbs)
    from math import lcm
    L = lcm(*lens) if lens else 1
    print(f"shape (3,2): n(cells)={n}, #SYT={len(syts)}")
    for o in orbs:
        print("  orbit length", len(o))
    assert len(syts) == 5 and n == 5
    assert lens == [2, 3] and L == 6
    assert all(n % d != 0 and len(syts) % d != 0 for d in lens)
    print(f"  => orbit lengths {lens}, lcm {L}: neither orbit length divides "
          f"n=5 or #SYT=5; lcm 6 divides neither 3 nor 5")

    print("\nAll attack numbers reproduced.")


if __name__ == "__main__":
    main()
