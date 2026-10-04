#!/usr/bin/env python3
"""Independent check for conjecture 00000001685 (Python 3 standard library only).

Method (different from the Lean proof): a graph G with N perfect matchings is
Pfaffian iff some orientation D has det(A_D) = N^2, because det(A_D) = Pf(A_D)^2
and |Pf(A_D)| <= N with equality iff all matchings have the same sign.
Determinants are computed exactly (Bareiss fraction-free elimination);
perfect matchings are counted by recursive enumeration.
"""
import itertools, sys

def det(M):
    """Exact integer determinant (Bareiss)."""
    A = [row[:] for row in M]
    n = len(A)
    sign, prev = 1, 1
    for k in range(n - 1):
        if A[k][k] == 0:
            for r in range(k + 1, n):
                if A[r][k] != 0:
                    A[k], A[r] = A[r], A[k]
                    sign = -sign
                    break
            else:
                return 0
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                A[i][j] = (A[i][j] * A[k][k] - A[i][k] * A[k][j]) // prev
        prev = A[k][k]
    return sign * A[n - 1][n - 1]

def matchings(n, E):
    adj = {v: set() for v in range(n)}
    for a, b in E:
        adj[a].add(b); adj[b].add(a)
    out = []
    def rec(free, cur):
        if not free:
            out.append(list(cur)); return
        v = min(free)
        for w in sorted(adj[v] & free):
            cur.append((v, w)); rec(free - {v, w}, cur); cur.pop()
    rec(frozenset(range(n)), [])
    return out

def skew(n, D):
    A = [[0] * n for _ in range(n)]
    for a, b in D:
        A[a][b] += 1; A[b][a] -= 1
    return A

def orientations(E, normalize, n):
    """All orientations, or (normalize=True) one per vertex-switching class:
    edges of a BFS spanning tree are kept in their given direction."""
    if not normalize:
        free = list(range(len(E)))
    else:
        seen, tree = {0}, set()
        frontier = [0]
        while frontier:
            v = frontier.pop()
            for i, (a, b) in enumerate(E):
                if v in (a, b):
                    w = b if a == v else a
                    if w not in seen:
                        seen.add(w); tree.add(i); frontier.append(w)
        assert len(seen) == n, "graph must be connected"
        free = [i for i in range(len(E)) if i not in tree]
    for bits in itertools.product([False, True], repeat=len(free)):
        flip = set(i for i, f in zip(free, bits) if f)
        yield [(b, a) if i in flip else (a, b) for i, (a, b) in enumerate(E)]

def pfaffian(n, E, normalize=False):
    N = len(matchings(n, E))
    count = 0
    for D in orientations(E, normalize, n):
        count += 1
        d = det(skew(n, D))
        assert d >= 0 and int(round(d ** 0.5)) ** 2 == d  # det of skew matrix is a square
        assert d <= N * N
        if d == N * N:
            return True, N, count
    return False, N, count

K33 = [(a, b) for a in range(3) for b in range(3, 6)]

def mobius(r):
    n = 2 * r
    return n, [(i, (i + 1) % n) for i in range(n)] + [(i, i + r) for i in range(r)]

def subdivide(n, E, counts):
    """Replace edge i by a path with counts[i] interior vertices."""
    out = []
    for (a, b), c in zip(E, counts):
        path = [a] + list(range(n, n + c)) + [b]
        n += c
        out += list(zip(path, path[1:]))
    return n, out

def pm_sign(w):
    inv = sum(1 for i in range(len(w)) for j in range(i + 1, len(w)) if w[j] < w[i])
    return -1 if inv % 2 else 1

def invariant_obstruction(n, E):
    """Parity obstruction used in the report/Lean: #PM even, every edge in an even
    number of perfect matchings, and the product of the terms is -1."""
    Ms = matchings(n, E)
    edge_count = {}
    prod = 1
    for M in Ms:
        w = []
        for (a, b) in M:
            e = (a, b) if (a, b) in E else (b, a)
            edge_count[e] = edge_count.get(e, 0) + 1
            w += [e[0], e[1]]          # reference orientation: as listed in E
        prod *= pm_sign(w)
    return len(Ms) % 2 == 0 and all(c % 2 == 0 for c in edge_count.values()) and prod == -1, len(Ms)

ok = True
def check(name, got, want):
    global ok
    flag = "ok" if got == want else "MISMATCH"
    if got != want:
        ok = False
    print(f"{name:58s} {got}  [{flag}]")

# 1. K_{3,3}, exhaustive over all 2^9 orientations
p, N, c = pfaffian(6, K33)
check("K33: Pfaffian?, #PM, orientations tried", (p, N, c), (False, 6, 512))
# 2. one edge subdivided twice (graph S of the report), all 2^11 orientations
n, E = subdivide(6, K33, [2, 0, 0, 0, 0, 0, 0, 0, 0])
p, N, c = pfaffian(n, E)
check("S (edge 03 subdivided twice): Pfaffian?, #PM, tried", (p, N, c), (False, 6, 2048))
# 3. two edges subdivided twice, all 2^13 orientations
n, E = subdivide(6, K33, [2, 0, 0, 0, 2, 0, 0, 0, 0])
p, N, c = pfaffian(n, E)
check("two edges subdivided twice: Pfaffian?, #PM, tried", (p, N, c), (False, 6, 8192))
# 4. every edge subdivided twice (24 vertices, 27 edges), up to vertex switching
n, E = subdivide(6, K33, [2] * 9)
p, N, c = pfaffian(n, E, normalize=True)
check("all 9 edges subdivided twice: Pfaffian?, #PM, classes", (p, N, c), (False, 6, 16))
# 5. every edge subdivided 4 times, up to vertex switching
n, E = subdivide(6, K33, [4] * 9)
p, N, c = pfaffian(n, E, normalize=True)
check("all 9 edges subdivided 4 times: Pfaffian?, #PM, classes", (p, N, c), (False, 6, 16))
# 6. parity obstruction holds for all 2^9 patterns of 0/2 subdivisions and some 0/2/4 ones
allok = True
for counts in itertools.product([0, 2], repeat=9):
    n, E = subdivide(6, K33, list(counts))
    good, N = invariant_obstruction(n, E)
    allok &= good and N == 6
for counts in [[4, 2, 0, 6, 0, 2, 0, 0, 4], [4] * 9, [6, 0, 0, 0, 0, 0, 0, 0, 2]]:
    n, E = subdivide(6, K33, counts)
    good, N = invariant_obstruction(n, E)
    allok &= good and N == 6
check("parity obstruction for 515 even subdivisions of K33", allok, True)
# 7. Moebius ladders (r rungs, 2r vertices)
for r, want in [(2, True), (3, False), (4, True), (5, False), (6, True), (7, False)]:
    n, E = mobius(r)
    p, N, c = pfaffian(n, E, normalize=True)
    check(f"Moebius ladder, {r} rungs ({2*r} vertices): Pfaffian?", p, want)
# 8. M_10 exhaustively over all 2^15 orientations (no switching reduction)
n, E = mobius(5)
p, N, c = pfaffian(n, E)
check("Moebius ladder 5 rungs, exhaustive: Pfaffian?, #PM, tried", (p, N, c), (False, 13, 32768))

# 9. Secondary: W = Wagner graph V_8 (4-rung Moebius ladder) with edge 01 subdivided twice.
#    It is Pfaffian, nonplanar (contains a K33 subdivision), has crossing number <= 1, and is
#    neither a Moebius ladder (it has degree-2 vertices) nor an even subdivision of K33
#    (|E| - |V| = 4, whereas every subdivision of K33 has |E| - |V| = 3).
n8, E8 = mobius(4)
n, E = subdivide(n8, E8, [2] + [0] * 11)
p, N, c = pfaffian(n, E)
check("W = V8 with edge 01 subdivided twice: Pfaffian?, #PM", (p, N), (True, 7))
deg = [sum(1 for e in E if v in e) for v in range(n)]
check("W: degrees 2 present, |E|-|V|", (deg.count(2), len(E) - n), (2, 4))
# explicit K33 subdivision inside V_8 - {04}: A = {1,3,6}, B = {2,5,7}
paths = [[1, 2], [1, 5], [1, 0, 7], [3, 2], [3, 7], [3, 4, 5], [6, 5], [6, 7], [6, 2]]
Eset = set(map(frozenset, E8))
good = all(frozenset(e) in Eset for P in paths for e in zip(P, P[1:]))
inner = [v for P in paths for v in P[1:-1]]
good &= len(inner) == len(set(inner)) and not set(inner) & {1, 2, 3, 5, 6, 7}
good &= sorted((P[0], P[-1]) for P in paths) == sorted((a, b) for a in (1, 3, 6) for b in (2, 5, 7))
check("V8 contains a subdivision of K33 (so V8 and W are nonplanar)", good, True)

print("ALL CHECKS PASSED" if ok else "SOME CHECK FAILED")
sys.exit(0 if ok else 1)
