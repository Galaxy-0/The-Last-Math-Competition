#!/usr/bin/env python3
"""Independent recomputation of the falsification of TLMC conjecture 00000000477.

Conjecture: for promotion on the set LE(P) of linear extensions of a poset P,
the lcm of the promotion orbit lengths divides #LE(P).

Counterexample checked here: the Ferrers poset of the Young diagram of
shape (3,2).  Expected result (matches the Lean certificate):

    #LE = 5
    promotion orbit lengths = [2, 3]
    lcm = 6
    6 divides 5 ?  False   ->  conjecture FALSIFIED

Run:  python3 reproduce.py
"""

from itertools import permutations
from math import gcd

# ---------------------------------------------------------------------------
# The Ferrers poset of shape (3,2): cells of the Young diagram, ordered
# componentwise.  Cells are (row, col); row 0 has 3 cells, row 1 has 2.
# ---------------------------------------------------------------------------
CELLS = [(0, 0), (0, 1), (0, 2), (1, 0), (1, 1)]


def le_cells(x, y):
    """Poset order: x <= y iff componentwise <= (Ferrers diagram order)."""
    return x[0] <= y[0] and x[1] <= y[1]


COMPARISONS = [(x, y) for x in CELLS for y in CELLS if x != y and le_cells(x, y)]


def is_linear_extension(perm):
    pos = {p: i for i, p in enumerate(perm)}
    return all(pos[x] < pos[y] for x, y in COMPARISONS)


def extension_to_tableau(perm):
    """A linear extension of the Ferrers poset is the same as an SYT:
    the entry of a cell is its position (1-based) in the extension."""
    pos = {p: i + 1 for i, p in enumerate(perm)}
    return (pos[(0, 0)], pos[(0, 1)], pos[(0, 2)]), (pos[(1, 0)], pos[(1, 1)])


def promote(tab):
    """Schutzenberger promotion on an SYT of size 5, shape (3,2):
    remove the corner entry, jeu-de-taquin slide the hole to an outer corner,
    write 6 into the hole, decrease every entry by 1."""
    rows = [list(tab[0]), list(tab[1])]

    def valid(r, c):
        return (r == 0 and c < 3) or (r == 1 and c < 2)

    hole = (0, 0)
    while True:
        r, c = hole
        right = (r, c + 1) if valid(r, c + 1) else None
        below = (r + 1, c) if valid(r + 1, c) else None
        if right is None and below is None:
            break  # hole reached an outer corner
        if right is not None and below is not None:
            mv = right if rows[right[0]][right[1]] <= rows[below[0]][below[1]] else below
        else:
            mv = right if right is not None else below
        rows[hole[0]][hole[1]] = rows[mv[0]][mv[1]]
        hole = mv
    rows[hole[0]][hole[1]] = 6
    rows = [[v - 1 for v in row] for row in rows]
    return (tuple(rows[0]), tuple(rows[1]))


def main():
    exts = [p for p in permutations(CELLS) if is_linear_extension(p)]
    n_le = len(exts)
    print("#LE(shape (3,2)) =", n_le)

    tabs = [extension_to_tableau(p) for p in exts]
    idx = {t: i for i, t in enumerate(tabs)}
    pr_map = [idx[promote(t)] for t in tabs]
    print("promotion permutation (index -> index):", pr_map)

    seen = [False] * len(tabs)
    orbits = []
    for i in range(len(tabs)):
        if not seen[i]:
            orb = []
            j = i
            while not seen[j]:
                seen[j] = True
                orb.append(j)
                j = pr_map[j]
            orbits.append(orb)
    lengths = sorted(len(o) for o in orbits)
    print("promotion orbit lengths:", lengths)

    L = 1
    for l in lengths:
        L = L * l // gcd(L, l)
    print("lcm of orbit lengths =", L)
    divides = (L % n_le == 0)
    print("does the lcm divide #LE ?", divides)

    print()
    for t in sorted(tabs):
        print("  SYT:", t)

    # Assertions matching the verdict line and the Lean certificate.
    assert n_le == 5, "expected #LE = 5"
    assert lengths == [2, 3], "expected orbit lengths [2, 3]"
    assert L == 6, "expected lcm = 6"
    assert not divides, "expected 6 does NOT divide 5"
    print()
    print("VERDICT: conjecture 00000000477 FALSIFIED "
          "(lcm=6 does not divide #LE=5)")


if __name__ == "__main__":
    main()
