#!/usr/bin/env python3
"""Independent check of conjecture 00000001091 (Python 3 standard library only).

Claim: the complete 10-arcs of PG(2,11) form a single projective equivalence class.

This script does NOT reuse the Lean tables.  It uses its own point normalisation
(last nonzero coordinate = 1), decides collinearity by a 3x3 determinant, and:
  1. enumerates all arcs of PG(2,11) containing the standard frame
     e1, e2, e3, (1,1,1) (every arc of size >= 4 is equivalent to one of these);
  2. lists the sizes of the complete ones; in particular, 84 complete 10-arcs contain the
     frame, and every one of the 252 incomplete 10-arcs through the frame lies on a conic;
  3. computes a canonical form (lexicographically least image over all 5040 frame maps)
     for each of the 84 complete 10-arcs: all 84 canonical forms coincide;
  4. computes the stabiliser of the representative (order 60, element orders of A5).
     By orbit counting, its orbit contains 5040/60 = 84 frame-containing arcs, i.e. all
     of them;
  5. reproduces the counts of the symmetry-reduced search used in the Lean proof.
"""
import itertools
from collections import Counter

q = 11


def norm(v):
    v = [x % q for x in v]
    for x in reversed(v):
        if x:
            s = pow(x, q - 2, q)
            return tuple(y * s % q for y in v)
    return None


PTS = sorted({norm(v) for v in itertools.product(range(q), repeat=3) if any(v)})
assert len(PTS) == q * q + q + 1 == 133
IDX = {p: i for i, p in enumerate(PTS)}
N = len(PTS)


def det(a, b, c):
    return (a[0] * (b[1] * c[2] - b[2] * c[1]) - a[1] * (b[0] * c[2] - b[2] * c[0])
            + a[2] * (b[0] * c[1] - b[1] * c[0])) % q


# secant masks: SEC[i][j] = bit mask of points on the line through points i != j
SEC = [[0] * N for _ in range(N)]
for i in range(N):
    for j in range(i + 1, N):
        m = 0
        for k in range(N):
            if det(PTS[i], PTS[j], PTS[k]) == 0:
                m |= 1 << k
        SEC[i][j] = SEC[j][i] = m
FULL = (1 << N) - 1

FRAME = [IDX[(1, 0, 0)], IDX[(0, 1, 0)], IDX[(0, 0, 1)], IDX[(1, 1, 1)]]


def is_arc(arc):
    return all(det(PTS[a], PTS[b], PTS[c]) for a, b, c in itertools.combinations(arc, 3))


def covered(arc):
    m = 0
    for a, b in itertools.combinations(arc, 2):
        m |= SEC[a][b]
    return m


# ---------------------------------------------------------------- 1. all arcs through frame
arcs_by_size = Counter()
complete_by_size = Counter()
complete10 = []
incomplete10 = []


def dfs(arc, blk, start):
    arcs_by_size[len(arc)] += 1
    if blk == FULL:
        complete_by_size[len(arc)] += 1
        if len(arc) == 10:
            complete10.append(tuple(sorted(arc)))
    elif len(arc) == 10:
        incomplete10.append(tuple(sorted(arc)))
    for c in range(start, N):
        if not (blk >> c) & 1:
            nb = blk
            for a in arc:
                nb |= SEC[a][c]
            dfs(arc + [c], nb, c + 1)


blk0 = covered(FRAME)
dfs(list(FRAME), blk0, 0)
print("arcs containing the frame, by size:", dict(sorted(arcs_by_size.items())))
print("complete arcs containing the frame, by size:", dict(sorted(complete_by_size.items())))
assert len(complete10) == 84 and len(incomplete10) == 252
for a in complete10:
    assert is_arc(a) and covered(a) == FULL
print("complete 10-arcs containing the frame: 84 (each re-checked: arc + every point on a secant)")


# 252 incomplete 10-arcs: each lies on a conic through its points
def conic_through(points):
    """Return coefficients of a conic through the given points (nullspace mod q)."""
    rows = [[x * x, y * y, z * z, x * y, x * z, y * z] for (x, y, z) in points]
    # Gaussian elimination mod q
    m = [r[:] for r in rows]
    piv = []
    r = 0
    for c in range(6):
        p = next((i for i in range(r, len(m)) if m[i][c] % q), None)
        if p is None:
            continue
        m[r], m[p] = m[p], m[r]
        s = pow(m[r][c], q - 2, q)
        m[r] = [x * s % q for x in m[r]]
        for i in range(len(m)):
            if i != r and m[i][c] % q:
                f = m[i][c]
                m[i] = [(x - f * y) % q for x, y in zip(m[i], m[r])]
        piv.append(c)
        r += 1
    free = [c for c in range(6) if c not in piv]
    if not free:
        return None
    sol = [0] * 6
    sol[free[0]] = 1
    for i, c in enumerate(piv):
        sol[c] = (-m[i][free[0]]) % q
    return sol


def on_conic(cf, p):
    x, y, z = p
    return (cf[0] * x * x + cf[1] * y * y + cf[2] * z * z + cf[3] * x * y + cf[4] * x * z
            + cf[5] * y * z) % q == 0


for a in incomplete10:
    pts = [PTS[i] for i in a]
    cf = conic_through(pts)
    assert cf is not None and all(on_conic(cf, p) for p in pts)
    conic = [i for i in range(N) if on_conic(cf, PTS[i])]
    assert len(conic) == 12 and is_arc(conic)
print("incomplete 10-arcs containing the frame: 252, each contained in a conic (a 12-arc)")


# ---------------------------------------------------------------- 2. projectivities
def minv(m):
    (a, b, c), (d, e, f), (g, h, i) = m
    D = (a * (e * i - f * h) - b * (d * i - f * g) + c * (d * h - e * g)) % q
    s = pow(D, q - 2, q)
    adj = [[e * i - f * h, c * h - b * i, b * f - c * e], [f * g - d * i, a * i - c * g, c * d - a * f],
           [d * h - e * g, b * g - a * h, a * e - b * d]]
    return [[x * s % q for x in r] for r in adj]


def mv(M, v):
    return tuple(sum(M[r][k] * v[k] for k in range(3)) % q for r in range(3))


def frame_map(P):
    """Matrix sending e1, e2, e3, (1,1,1) to the points P[0..3] (projectively)."""
    p = [PTS[i] for i in P]
    C = [[p[c][r] for c in range(3)] for r in range(3)]
    lam = mv(minv(C), p[3])
    return [[lam[c] * p[c][r] % q for c in range(3)] for r in range(3)]


def image(M, arc):
    return tuple(sorted(IDX[norm(mv(M, PTS[a]))] for a in arc))


def canon(arc):
    return min(image(minv(frame_map(P)), arc) for P in itertools.permutations(arc, 4))


forms = {canon(a) for a in complete10}
print("distinct canonical forms among the 84 complete 10-arcs:", len(forms))
assert len(forms) == 1

rep = complete10[0]
stab = []
for P in itertools.permutations(rep, 4):
    M = minv(frame_map(P))     # sends P to the frame
    if image(M, rep) == rep:
        stab.append(M)
print("stabiliser order of a complete 10-arc:", len(stab), "->", 5040 // len(stab),
      "frame-containing arcs in its orbit (= all 84)")
assert len(stab) == 60 and 5040 // 60 == 84


def order(M):
    # order of the induced permutation of the points: smallest k with M^k = id on points
    k, cur = 1, [[int(r == c) for c in range(3)] for r in range(3)]
    while True:
        cur = [[sum(cur[r][t] * M[t][c] for t in range(3)) % q for c in range(3)] for r in range(3)]
        if all(norm(mv(cur, p)) == p for p in PTS):
            return k
        k += 1


print("element orders in the stabiliser:", dict(sorted(Counter(order(M) for M in stab).items())),
      "(those of A5: {1:1, 2:15, 3:20, 5:24})")
PGL = q ** 3 * (q ** 3 - 1) * (q ** 2 - 1)
print("|PGL(3,11)| =", PGL, "; number of complete 10-arcs in PG(2,11) =", PGL // 60)
print("representative:", [PTS[i] for i in rep])

# literature cross-check: Ball-Lavrauw, "Planar arcs" (JCTA 2018), Example 3 / Corollary 8
BL = [(1, 0, 0), (0, 1, 0), (0, 0, 1), (1, 8, 7), (1, 5, 2), (1, 3, 8), (1, 4, 1), (1, 7, 6),
      (1, 9, 4), (1, 10, 5)]
bl = tuple(sorted(IDX[norm(p)] for p in BL))
assert len(bl) == 10 and is_arc(bl) and covered(bl) == FULL and canon(bl) in forms
print("Ball-Lavrauw Example 3 arc: complete 10-arc, same canonical form as ours")

# ---------------------------------------------------------------- 3. Lean search numbers
# Lean numbers points as 11a+b -> (1,a,b), 121+b -> (0,1,b), 132 -> (0,0,1); frame = 0,121,132,12.
def lcoord(i):
    if i < 121:
        return (1, i // 11, i % 11)
    if i < 132:
        return (0, 1, i - 121)
    return (0, 0, 1)


LP = [lcoord(i) for i in range(133)]
LT = {norm(LP[i]): i for i in range(133)}
LF = [0, 121, 132, 12]


def lcol(a, b, c):
    return det(LP[a], LP[b], LP[c]) == 0


cands = [s for s in range(133) if s not in LF
         and not any(lcol(a, b, s) for a, b in itertools.combinations(LF, 2))]
G = [minv(frame_map([IDX[norm(LP[i])] for i in P])) for P in itertools.permutations(LF)]


def lact(M, i):
    # M acts in the verify.py basis; convert via coordinates (same vector space)
    return LT[norm(mv(M, LP[i]))]


orbits, seen = [], set()
for c in cands:
    if c not in seen:
        o = sorted({lact(Minv, c) for Minv in [minv(M) for M in G]})
        orbits.append(o)
        seen |= set(o)
print("orbits of the frame stabiliser on the 72 candidates:", [len(o) for o in orbits],
      "representatives", [o[0] for o in orbits])
assert [len(o) for o in orbits] == [12, 24, 24, 12] and [o[0] for o in orbits] == [25, 26, 27, 37]
nodes, leaves, complete_leaves = 0, 0, 0
excl = set()
for o in orbits:
    r = o[0]
    ch0 = LF + [r]
    rest = [d for d in range(133) if d not in ch0 and d not in excl
            and not any(lcol(a, b, d) for a, b in itertools.combinations(ch0, 2))]

    def srch(k, ch, rest):
        global nodes, leaves, complete_leaves
        nodes += 1
        if k == 0:
            leaves += 1
            if all(p in ch or any(lcol(a, b, p) for a, b in itertools.combinations(ch, 2))
                   for p in range(133)):
                complete_leaves += 1
            return
        for j, c in enumerate(rest):
            r2 = rest[j + 1:]
            if len(r2) < k - 1:
                continue
            srch(k - 1, ch + [c], [d for d in r2 if not any(lcol(a, c, d) for a in ch)])

    srch(5, ch0, rest)
    excl |= set(o)
print("symmetry-reduced search (as in Lean): nodes", nodes, "leaves", leaves,
      "complete leaves", complete_leaves)
assert (nodes, leaves, complete_leaves) == (1455, 56, 13)
print("ALL CHECKS PASSED: the complete 10-arcs of PG(2,11) form a single class.")
