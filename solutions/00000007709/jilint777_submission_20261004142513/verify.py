#!/usr/bin/env python3
"""Independent check (Python 3 standard library only) for conjecture 00000007709.

Claim refuted: "the order k of a convex rep-tile must be a perfect square or k = 2".
Counterexample: the right triangle with legs 1:2 is a rep-5 tile.

The Lean proof checks the tiling by case analysis on linear inequalities. This script
uses a different method with exact rational arithmetic:
  (1) every piece is the image of T under an explicit similarity z -> (a*conj(z)+b)/5
      with |a|^2 = 5, i.e. ratio 1/sqrt(5); the pieces are pairwise congruent
      (equal sorted squared side lengths);
  (2) every piece lies in T (its vertices lie in T and T is convex);
  (3) the interiors are pairwise disjoint (separating-axis test: for two convex
      polygons, some edge line of one of them weakly separates them);
  (4) the areas of the pieces add up to the area of T.
(2)-(4) together imply that the pieces cover T: the uncovered part of T would be
relatively open in T, so it would have positive area if it were nonempty.
As an extra sanity check, a fine rational grid is tested point by point.

It also checks the 30-60-90 remark from the report (minimal-order reading) exactly,
with numbers in Q(sqrt 3).
"""
from fractions import Fraction as F
from itertools import combinations
import sys

ok_all = True


def check(cond, msg):
    global ok_all
    print(("ok   " if cond else "FAIL ") + msg)
    if not cond:
        ok_all = False


# ---------------------------------------------------------------- the rep-5 tiling
A, B, C = (0, 0), (10, 0), (0, 5)
D, M1, M2, M3 = (2, 4), (1, 2), (6, 2), (5, 0)
T = [A, B, C]
pieces = [[A, D, C], [A, M3, M1], [M3, B, M2], [M1, M2, D], [M3, M2, M1]]
# f_i(z) = (a_i * conj(z) + b_i) / 5   (big triangle -> piece i)
maps = [(complex(-1, -2), complex(10, 20)), (complex(2, -1), complex(5, 10)),
        (complex(2, -1), complex(30, 10)), (complex(2, -1), complex(10, 20)),
        (complex(-2, 1), complex(25, 0))]


def d2(p, q):
    return (p[0] - q[0]) ** 2 + (p[1] - q[1]) ** 2


def cross(o, a, b):
    return (a[0] - o[0]) * (b[1] - o[1]) - (a[1] - o[1]) * (b[0] - o[0])


def area2(poly):  # twice the signed area
    return sum(poly[i][0] * poly[(i + 1) % len(poly)][1] - poly[(i + 1) % len(poly)][0] * poly[i][1]
               for i in range(len(poly)))


def apply(m, p):
    a, b = m
    ar, ai, br, bi = int(a.real), int(a.imag), int(b.real), int(b.imag)
    x, y = p
    # (ar + ai i)(x - y i) + (br + bi i)
    return (F(ar * x + ai * y + br, 5), F(ai * x - ar * y + bi, 5))


def inside(poly, p, strict=False):
    n = len(poly)
    vals = [cross(poly[i], poly[(i + 1) % n], p) for i in range(n)]
    return all(v > 0 for v in vals) if strict else all(v >= 0 for v in vals)


big_sides = sorted(d2(*e) for e in combinations(T, 2))
check(big_sides == [25, 100, 125], f"T = ABC has squared sides {big_sides} (legs 5 and 10: ratio 1:2, right angle at A)")
check(d2(A, B) + d2(A, C) == d2(B, C), "right angle at A (Pythagoras)")
check(area2(T) > 0, "T is a counterclockwise nondegenerate triangle (convex)")

for i, (poly, m) in enumerate(zip(pieces, maps), 1):
    a = m[0]
    norm = int(a.real) ** 2 + int(a.imag) ** 2
    check(norm == 5, f"piece {i}: |a|^2 = 5, so f_{i} has squared ratio 5/25 = 1/5")
    img = [apply(m, v) for v in T]
    check(sorted(img) == sorted((F(x), F(y)) for x, y in poly),
          f"piece {i}: f_{i}(A,B,C) = {[(str(x), str(y)) for x, y in img]} = vertices of piece {i}")
    sides = sorted(d2(*e) for e in combinations(poly, 2))
    check(sides == [5, 20, 25], f"piece {i}: squared sides {sides} = (1/5) * {big_sides}")
    check(area2(poly) > 0, f"piece {i}: counterclockwise nondegenerate triangle")
    check(all(inside(T, v) for v in poly), f"piece {i}: vertices lie in T, so piece {i} lies in T")

check(sum(area2(p) for p in pieces) == area2(T),
      f"areas: sum of doubled areas {sum(area2(p) for p in pieces)} = doubled area of T {area2(T)}")


def separated(P, Q):
    for poly, other in ((P, Q), (Q, P)):
        n = len(poly)
        for i in range(n):
            if all(cross(poly[i], poly[(i + 1) % n], q) <= 0 for q in other):
                return True
    return False


for (i, P), (j, Q) in combinations(enumerate(pieces, 1), 2):
    check(separated(P, Q), f"pieces {i},{j}: an edge line separates them, interiors disjoint")

# grid sanity check with exact rationals
N = 24
bad_cover = bad_overlap = 0
cnt = 0
for u in range(0, 10 * N + 1):
    for v in range(0, 5 * N + 1):
        p = (F(u, N), F(v, N))
        if inside(T, p):
            cnt += 1
            if not any(inside(q, p) for q in pieces):
                bad_cover += 1
            if sum(inside(q, p, True) for q in pieces) > 1:
                bad_overlap += 1
check(bad_cover == 0 and bad_overlap == 0,
      f"grid check: {cnt} rational points of T with step 1/{N}, each in some piece, none in two interiors")

check(all(m * m != 5 for m in range(6)) and 5 != 2, "5 is not a perfect square and 5 != 2")

# ---------------------------------------------------------------- 30-60-90 remark
# numbers a + b*sqrt(3) with a, b rational, as pairs


def q_add(x, y): return (x[0] + y[0], x[1] + y[1])
def q_sub(x, y): return (x[0] - y[0], x[1] - y[1])
def q_mul(x, y): return (x[0] * y[0] + 3 * x[1] * y[1], x[0] * y[1] + x[1] * y[0])


def q_sign(x):
    a, b = x  # sign of a + b sqrt3
    if b == 0:
        return (a > 0) - (a < 0)
    if a == 0:
        return (b > 0) - (b < 0)
    if a > 0 and b > 0:
        return 1
    if a < 0 and b < 0:
        return -1
    # opposite signs: compare a^2 with 3 b^2
    s = (a * a > 3 * b * b) - (a * a < 3 * b * b)
    return s if a > 0 else -s


def Q(a, b=0): return (F(a), F(b))
def qd2(p, q):
    dx, dy = q_sub(p[0], q[0]), q_sub(p[1], q[1])
    return q_add(q_mul(dx, dx), q_mul(dy, dy))
def qcross(o, a, b):
    return q_sub(q_mul(q_sub(a[0], o[0]), q_sub(b[1], o[1])), q_mul(q_sub(a[1], o[1]), q_sub(b[0], o[0])))


O, Ap, Bp = (Q(0), Q(0)), (Q(0, 1), Q(0)), (Q(0), Q(1))      # legs 1 and sqrt3, hypotenuse 2
P, Qm = (Q(0, F(1, 3)), Q(0)), (Q(0, F(1, 2)), Q(F(1, 2)))     # P = (1/sqrt3, 0), Q = midpoint of AB
T3 = [O, Ap, Bp]
pcs3 = [[O, P, Bp], [P, Qm, Bp], [P, Ap, Qm]]
big3 = sorted(qd2(*e) for e in combinations(T3, 2))
check(big3 == [Q(1), Q(3), Q(4)], "30-60-90 triangle: squared sides 1, 3, 4")
for k, pc in enumerate(pcs3, 1):
    s = sorted(qd2(*e) for e in combinations(pc, 2))
    check(s == [Q(F(1, 3)), Q(1), Q(F(4, 3))], f"30-60-90 piece {k}: squared sides 1/3, 1, 4/3 (ratio 1/sqrt3)")
    check(q_sign(qcross(*pc)) > 0, f"30-60-90 piece {k}: counterclockwise nondegenerate")
ar = lambda pc: qcross(*pc)
tot = Q(0)
for pc in pcs3:
    tot = q_add(tot, ar(pc))
check(tot == ar(T3), "30-60-90: piece areas add up to the area of the triangle")
for v in [P, Qm]:
    check(all(q_sign(qcross(T3[i], T3[(i + 1) % 3], v)) >= 0 for i in range(3)), "30-60-90: new vertex lies in the triangle")


def qsep(P1, P2):
    for poly, other in ((P1, P2), (P2, P1)):
        for i in range(3):
            if all(q_sign(qcross(poly[i], poly[(i + 1) % 3], q)) <= 0 for q in other):
                return True
    return False


check(all(qsep(x, y) for x, y in combinations(pcs3, 2)), "30-60-90: pieces have pairwise disjoint interiors")
# not rep-2: hypotenuse 2 is not a sum of one or two side lengths of pieces with sides {1, sqrt3, 2}/sqrt2.
# (u+v)/sqrt2 = 2  <=>  (u+v)^2 = 8 ;  u/sqrt2 = 2 <=> u^2 = 8.
lens = [Q(1), Q(0, 1), Q(2)]
sums = [q_mul(u, u) for u in lens] + [q_mul(q_add(u, v), q_add(u, v)) for u in lens for v in lens]
check(all(s != Q(8) for s in sums), "30-60-90: hypotenuse 2 is not a sum of <= 2 piece sides of a 2-piece dissection")

print("ALL CHECKS PASSED" if ok_all else "SOME CHECKS FAILED")
sys.exit(0 if ok_all else 1)
