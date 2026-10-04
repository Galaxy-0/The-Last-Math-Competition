#!/usr/bin/env python3
"""Independent check (Python 3 standard library only) for conjecture 00000001028.

1. Reads the seven resolutions R4, R16, R28, R40, R52, R64, R76 from lean4/Main.lean.
2. Checks each is a Kirkman quadruple system with a method different from the Lean
   bitmask checker: it enumerates all pairs inside blocks and compares multisets.
3. Re-derives each design from its geometric/algebraic description:
   AG(2,4), AG(3,4) lines; Hermitian unital U(3) in PG(2,9); lines of PG(3,3);
   1-rotational developments of base blocks in Z_51 and Z_75 (incl. the difference property).
4. Counts the admissible values v = 4 (mod 12) below 316 and the resulting bound.
"""
import ast
import itertools
import os
import re
import sys
from collections import Counter

HERE = os.path.dirname(os.path.abspath(__file__))
SRC = open(os.path.join(HERE, "lean4", "Main.lean"), encoding="utf-8").read()


def read_resolution(v):
    m = re.search(r"def R%d : Resolution := (\[.*?\])\n\n" % v, SRC, re.S)
    assert m, "R%d not found" % v
    return ast.literal_eval(m.group(1))


def check_kqs(v, R):
    """Resolvable 2-(v,4,1) design, checked by explicit pair counting."""
    blocks = [tuple(B) for C in R for B in C]
    for B in blocks:
        assert len(B) == 4 and len(set(B)) == 4 and all(0 <= x < v for x in B)
    for C in R:
        assert sorted(x for B in C for x in B) == list(range(v)), "class is not a partition"
    pairs = Counter(frozenset(p) for B in blocks for p in itertools.combinations(B, 2))
    allpairs = {frozenset(p) for p in itertools.combinations(range(v), 2)}
    assert set(pairs) == allpairs and set(pairs.values()) <= {1}, "pair condition"
    assert len(blocks) == v * (v - 1) // 12 and len(R) == (v - 1) // 3
    return len(R), len(blocks)


def same_design(R, blocks):
    return sorted(sorted(B) for C in R for B in C) == sorted(sorted(B) for B in blocks)


# ---------- GF(4): {0,1,2,3}, addition = xor, 2 = w, 3 = w^2 ----------
def gf4_mul(a, b):
    if a == 0 or b == 0:
        return 0
    log = {1: 0, 2: 1, 3: 2}
    exp = [1, 2, 3]
    return exp[(log[a] + log[b]) % 3]


def ag_lines(n):
    vecs = list(itertools.product(range(4), repeat=n))
    enc = lambda p: sum(c * 4 ** i for i, c in enumerate(p))
    lines = set()
    for p in vecs:
        for d in vecs:
            if any(d):
                lines.add(frozenset(enc(tuple(p[i] ^ gf4_mul(t, d[i]) for i in range(n)))
                                    for t in range(4)))
    return [sorted(L) for L in lines]


# ---------- GF(9) = GF(3)[i], i^2 = -1; element a+bi as (a,b) ----------
G9 = [(a, b) for a in range(3) for b in range(3)]


def m9(x, y):
    return ((x[0] * y[0] - x[1] * y[1]) % 3, (x[0] * y[1] + x[1] * y[0]) % 3)


def a9(x, y):
    return ((x[0] + y[0]) % 3, (x[1] + y[1]) % 3)


def unital_points():
    Z = (0, 0)
    inv = {x: next(y for y in G9 if m9(x, y) == (1, 0)) for x in G9 if x != Z}

    def norm(v):
        for c in v:
            if c != Z:
                return tuple(m9(e, inv[c]) for e in v)

    def p4(x):
        r = (1, 0)
        for _ in range(4):
            r = m9(r, x)
        return r
    pts = sorted({norm(v) for v in itertools.product(G9, repeat=3) if any(c != Z for c in v)})
    assert len(pts) == 91
    U = [p for p in pts if a9(a9(p4(p[0]), p4(p[1])), p4(p[2])) == Z]
    assert len(U) == 28
    return U


def det3_gf9(a, b, c):
    t = (0, 0)
    for (i, j, k), s in [((0, 1, 2), 1), ((1, 2, 0), 1), ((2, 0, 1), 1),
                         ((0, 2, 1), -1), ((2, 1, 0), -1), ((1, 0, 2), -1)]:
        u = m9(m9(a[i], b[j]), c[k])
        if s < 0:
            u = ((-u[0]) % 3, (-u[1]) % 3)
        t = a9(t, u)
    return t


def unital_blocks():
    U = unital_points()
    blocks = set()
    for a, b in itertools.combinations(range(28), 2):
        blocks.add(frozenset(c for c in range(28)
                             if det3_gf9(U[a], U[b], U[c]) == (0, 0)))
    assert all(len(B) == 4 for B in blocks) and len(blocks) == 63
    return [sorted(B) for B in blocks]


def pg33_lines():
    q = 3

    def norm(v):
        for a in v:
            if a % q:
                inv = pow(a, q - 2, q)
                return tuple(x * inv % q for x in v)
    pts = sorted({norm(v) for v in itertools.product(range(q), repeat=4) if any(v)})
    idx = {p: i for i, p in enumerate(pts)}
    lines = set()
    for a, b in itertools.combinations(pts, 2):
        lines.add(frozenset(idx[norm(tuple((x * a[k] + y * b[k]) % q for k in range(4)))]
                            for x in range(q) for y in range(q) if x or y))
    assert len(pts) == 40 and len(lines) == 130
    return [sorted(L) for L in lines]


def one_rotational(m, base):
    """Points Z_{3m} and infinity = 3m; class j = {j, j+m, j+2m, inf} + (base + j + m k)."""
    N = 3 * m
    # difference property: base-block differences cover Z_N \ {0, m, 2m} exactly once
    diffs = Counter((x - y) % N for B in base for x in B for y in B if x != y)
    assert set(diffs) == set(range(1, N)) - {m, 2 * m} and set(diffs.values()) == {1}
    # residues mod m of base-block points partition {1, ..., m-1}
    assert sorted(x % m for B in base for x in B) == list(range(1, m))
    R = []
    for j in range(m):
        C = [[j, j + m, j + 2 * m, N]]
        for B in base:
            for k in range(3):
                C.append(sorted((x + j + m * k) % N for x in B))
        R.append(C)
    return R


def same_resolution(R, S):
    norm = lambda R: sorted(sorted(sorted(B) for B in C) for C in R)
    return norm(R) == norm(S)


def main():
    ok = True
    res = {v: read_resolution(v) for v in (4, 16, 28, 40, 52, 64, 76)}
    for v, R in res.items():
        r, b = check_kqs(v, R)
        print("v = %2d: KQS verified (%d parallel classes, %d blocks)" % (v, r, b))
    # geometric / algebraic origin
    assert same_design(res[16], ag_lines(2)); print("R16 = lines of AG(2,4)")
    assert same_design(res[64], ag_lines(3)); print("R64 = lines of AG(3,4)")
    assert same_design(res[28], unital_blocks()); print("R28 = secant lines of the Hermitian unital U(3) in PG(2,9)")
    assert same_design(res[40], pg33_lines()); print("R40 = lines of PG(3,3) (13 spreads)")
    b52 = [[1, 2, 20, 24], [4, 25, 12, 49], [5, 10, 45, 30], [6, 9, 48, 50]]
    assert same_resolution(res[52], one_rotational(17, b52)); print("R52 = 1-rotational development over Z_51 (difference property checked)")
    b76 = [[1, 34, 47, 48], [2, 33, 67, 69], [3, 56, 7, 71], [4, 61, 13, 16], [5, 60, 37, 43], [14, 65, 70, 49]]
    assert same_resolution(res[76], one_rotational(25, b76)); print("R76 = 1-rotational development over Z_75 (difference property checked)")
    # counting
    adm = [v for v in range(316) if v % 12 == 4]
    print("admissible v < 316:", len(adm), "values", adm[0], "...", adm[-1])
    known = sorted(res)
    print("KQS exhibited for", known)
    bound_strict = len([v for v in adm if v not in known])
    bound_le = len([v for v in range(317) if v % 12 == 4 and v not in known])
    print("exceptional values below 316: at most", bound_strict, "(at most", bound_le, "if 316 is included)")
    ok = ok and bound_strict == 19 and bound_le == 20 and len(adm) == 26
    if ok and bound_le < 21:
        print("the clause 'exactly 21 exceptional values below v0 = 316' is FALSE")
        print("ALL CHECKS PASSED")
        return 0
    print("CHECK FAILED")
    return 1


if __name__ == "__main__":
    sys.exit(main())
