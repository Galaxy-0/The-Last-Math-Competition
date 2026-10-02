#!/usr/bin/env python3
"""Reproduce the disproof of TLMC conjecture 00000001236.

Conjecture (paraphrase): min weight over recurrent configurations equals
  maxstable_weight - S(M),
where M = rounding of the inverse of the (V-1)x(V-1) reduced Laplacian and
S(M) is its "row-minimal sum" (checked under BOTH readings: sum of row
minima, and minimum row sum). The minimal recurrent configuration is
claimed unique up to isomorphism.

Counterexample graph G: path 1-2-3 with a sink attached to vertex 3
(P3 + terminal sink). Everything is computed exactly (fractions).
"""

from fractions import Fraction
from itertools import product

# ---------- exact linear algebra ----------
def inverse(mat):
    n = len(mat)
    a = [[Fraction(int(x)) for x in row]
         + [Fraction(int(i == j)) for j in range(n)]
         for i, row in enumerate(mat)]
    for c in range(n):
        p = next(r for r in range(c, n) if a[r][c] != 0)
        a[c], a[p] = a[p], a[c]
        pv = a[c][c]
        a[c] = [x / pv for x in a[c]]
        for r in range(n):
            if r != c and a[r][c] != 0:
                f = a[r][c]
                a[r] = [x - f * y for x, y in zip(a[r], a[c])]
    return [row[n:] for row in a]


def det(mat):
    a = [[Fraction(x) for x in row] for row in mat]
    n, d = len(a), Fraction(1)
    for c in range(n):
        p = next(r for r in range(c, n) if a[r][c] != 0)
        if p != c:
            a[c], a[p] = a[p], a[c]; d = -d
        d *= a[c][c]
        for r in range(c + 1, n):
            f = a[r][c] / a[c][c]
            a[r] = [x - f * y for x, y in zip(a[r], a[c])]
    return d


def recurrent_configs(nonsink_degrees, adjacency):
    """All recurrent configs on the non-sink vertices (with sink).

    Two independent classical characterizations; assert they agree.
    adjacency[i] = list of neighbor indices among non-sink vertices
    (sink adjacency is nonsink_degrees[i] - len(adjacency[i]) edges).
    """
    n = len(adjacency)
    stable = []
    for c in product(*[range(d) for d in nonsink_degrees]):
        stable.append(tuple(c))

    def burning(c):
        # Dhar's burning test; the sink burns from the start, so a vertex's
        # initially-burning neighbours are its edges to the sink.
        burned = [False] * n
        for _ in range(n):
            progressed = False
            for v in range(n):
                if not burned[v]:
                    b = (nonsink_degrees[v] - len(adjacency[v])
                         + sum(burned[u] for u in adjacency[v]))
                    if c[v] >= nonsink_degrees[v] - b:
                        burned[v] = True; progressed = True
            if all(burned):
                return True
            if not progressed:
                return False
        return all(burned)

    def no_forbidden(c):
        # c recurrent iff it has no nonempty forbidden subconfiguration
        for r in range(1, n + 1):
            for S in product(range(n), repeat=r):
                S = set(S)
                if len(S) != r:
                    continue
                if all(c[v] < sum(1 for u in adjacency[v] if u in S)
                       for v in S):
                    return False
        return True

    rec = [c for c in stable if burning(c)]
    assert rec == [c for c in stable if no_forbidden(c)]
    return rec


def analyse(name, degrees, adjacency):
    n = len(adjacency)
    L = [[(degrees[i] if i == j else 0) for j in range(n)] for i in range(n)]
    for i in range(n):
        for j in adjacency[i]:
            L[i][j] -= 1
    d = det(L)
    inv = inverse(L)
    integral = all(x.denominator == 1 for r in inv for x in r)
    Mint = [[int(x) for x in r] for r in inv]  # rounding is exact here
    sum_rowmin = sum(min(r) for r in Mint)     # reading A
    min_rowsum = min(sum(r) for r in Mint)     # reading B
    maxstable = tuple(g - 1 for g in degrees)
    recs = recurrent_configs(degrees, adjacency)
    minrec = min(sum(c) for c in recs)
    print(f"== {name}")
    print(f"  reduced Laplacian L = {L}, det L = {d}")
    print(f"  L^-1 = {Mint}  (integral: {integral}; any rounding = identity)")
    print(f"  row minima sums: reading A (sum of row minima) = {sum_rowmin},"
          f" reading B (minimum row sum) = {min_rowsum}")
    print(f"  max-stable = {maxstable}, weight = {sum(maxstable)}")
    print(f"  recurrent configs: {recs}")
    print(f"  minimal recurrent weight = {minrec}")
    for label, S in (("A", sum_rowmin), ("B", min_rowsum)):
        pred = sum(maxstable) - S
        print(f"  formula (reading {label}): {sum(maxstable)} - {S} = {pred}"
              f"  {'MATCH' if pred == minrec else 'MISMATCH'}")
    print()
    return minrec, sum_rowmin, min_rowsum, sum(maxstable)


# G1: the counterexample. Path 1-2-3 + sink attached to 3.
g1 = analyse("P3 + sink", [1, 2, 2], [[1], [0, 2], [1]])

# corroboration: P2 + sink and P4 + sink (both fail as well)
analyse("P2 + sink", [1, 2], [[1], [0]])
analyse("P4 + sink", [1, 2, 2, 2], [[1], [0, 2], [1, 3], [2]])

m, A, B, ms = g1
assert m == 2 and ms == 2 and A == 3 and B == 3, "unexpected numbers"
assert ms - A == -1 and ms - B == -1 and -1 != m
print("CONJECTURE 00000001236 DISPROVED: on P3+sink the formula predicts -1 "
      "under BOTH readings of 'row-minimal sum', the true minimum recurrent "
      "weight is 2 (unique recurrent configuration (0,1,1), since det L = 1).")
