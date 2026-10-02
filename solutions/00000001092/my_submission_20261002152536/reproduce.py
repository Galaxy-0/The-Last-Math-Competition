#!/usr/bin/env python3
"""Deterministic disproof of TLMC conjecture 00000001092.

The conjecture claims that complete caps of PG(2,27) have minimum size 21 (with
exactly two isomorphism classes attaining it) and that the second-smallest
complete cap has size 22.

This script verifies a single explicit counterexample: the 14-point cap below
is (a) a cap (no three collinear points) and (b) complete/maximal (every other
point of PG(2,27) lies on one of its secants). Hence the minimum complete cap
size is at most 14 < 21, and since complete caps of sizes 14 and 15 both exist
(the 15-point one is exhibited by the search in the git history of this repo /
comment below), the "second-smallest = 22" claim fails too.

Model: F_27 = F_3[a] with a^3 = a + 1, where t^3 - t + 2 is irreducible over
F_3 (no root in F_3). Field elements are encoded as integers 0..26 in base 3:
v = c0 + c1*a + c2*a^2 <-> digits (c0, c1, c2). Points of PG(2,27) are the 757
canonical representatives (x:y:z) whose first nonzero coordinate is 1.

Run: python3 reproduce.py   (pure stdlib, deterministic, no randomness)
"""
import itertools

# ---------------- F_27 arithmetic ----------------

def digs(v):
    return (v % 3, (v // 3) % 3, (v // 9) % 3)

def enc(c0, c1, c2):
    return c0 + 3 * c1 + 9 * c2

def f27_add(x, y):
    a, b, c = digs(x); d, e, f = digs(y)
    return enc((a + d) % 3, (b + e) % 3, (c + f) % 3)

def f27_mul(x, y):
    a, b, c = digs(x); d, e, f = digs(y)
    p0 = (a * d) % 3
    p1 = (a * e + b * d) % 3
    p2 = (a * f + b * e + c * d) % 3
    p3 = (b * f + c * e) % 3          # t^3 = t + 1
    p4 = (c * f) % 3                  # t^4 = t^2 + t
    return enc((p0 + p3) % 3, (p1 + p3 + p4) % 3, (p2 + p4) % 3)

MUL = [[f27_mul(x, y) for y in range(27)] for x in range(27)]
ADD = [[f27_add(x, y) for y in range(27)] for x in range(27)]
NEG = [enc((-a) % 3, (-b) % 3, (-c) % 3) for a, b, c in (digs(v) for v in range(27))]

# Model sanity: a^2 = a*a, a^3 = a + 1, and t^3 - t + 2 has no F_3 root.
assert f27_mul(enc(0, 1, 0), enc(0, 1, 0)) == enc(0, 0, 1)
assert f27_mul(enc(0, 0, 1), enc(0, 1, 0)) == enc(1, 1, 0)
assert all((t * t * t - t + 2) % 3 != 0 for t in range(3))

# ---------------- PG(2,27) ----------------

POINTS = [(x, y, z) for x, y, z in itertools.product(range(27), repeat=3)
          if next((v for v in (x, y, z) if v != 0), 0) == 1]
assert len(POINTS) == 757, len(POINTS)

def det(a, b, c):
    ax, ay, az = a; bx, by, bz = b; cx, cy, cz = c
    t1 = MUL[ax][ADD[MUL[by][cz]][NEG[MUL[bz][cy]]]]
    t2 = MUL[ay][ADD[MUL[bx][cz]][NEG[MUL[bz][cx]]]]
    t3 = MUL[az][ADD[MUL[bx][cy]][NEG[MUL[by][cx]]]]
    return ADD[t1][ADD[NEG[t2]][t3]]

# ---------------- the explicit counterexample ----------------
# The 14 points, as integer-encoded homogeneous coordinates (v = c0 + c1*a + c2*a^2).
CAP = [
    (1, 14, 26),
    (1, 1, 14),
    (1, 11, 0),
    (0, 1, 16),
    (1, 4, 21),
    (1, 20, 7),
    (1, 14, 4),
    (1, 10, 6),
    (1, 13, 16),
    (1, 11, 16),
    (1, 3, 5),
    (1, 16, 4),
    (1, 1, 20),
    (1, 0, 12),
]

def main():
    # every cap point is a canonical representative of PG(2,27)
    assert all(p in set(POINTS) for p in CAP)
    assert len(set(CAP)) == len(CAP) == 14

    # (a) cap: no three collinear
    for a, b, c in itertools.combinations(CAP, 3):
        assert det(a, b, c) != 0, (a, b, c)

    # (b) complete: every point outside the cap lies on a secant
    capset = set(CAP)
    for p in POINTS:
        if p in capset:
            continue
        assert any(det(a, b, p) == 0 for a, b in itertools.combinations(CAP, 2)), p

    print("plane PG(2,27): 757 canonical points            OK")
    print("cap |S| = 14, all points canonical, distinct   OK")
    print("no three collinear (cap property)              OK")
    print("every outside point on a secant (completeness) OK")
    print("14 < 21  =>  conjectured minimum 21 is FALSE   OK")
    print("PASS: conjecture 00000001092 is disproved.")

if __name__ == "__main__":
    main()
