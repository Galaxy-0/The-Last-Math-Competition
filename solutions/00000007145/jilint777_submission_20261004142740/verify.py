#!/usr/bin/env python3
"""Independent check for conjecture 00000007145 (Python 3 standard library only).

Method (different from the Lean proof): the graph of each polytope is computed
from its FACETS.  Facets are found by brute force over all d-subsets of points
(exact integer hyperplanes); the smallest face containing two vertices p, q is the
intersection of all facets containing both, and {p, q} is an edge iff that
intersection is exactly {p, q}.  Hamiltonicity is then decided by exhaustive
depth-first search.  Extra readings: the simplicial triakis octahedron and the
facet-adjacency (dual) graph of the cuboctahedron.  The Lean tables (edges with exposing functionals, non-edges
with convex-combination certificates) are re-checked with exact arithmetic too.
"""
from fractions import Fraction
from itertools import combinations, product
import os
import sys

def det(M):
    M = [[Fraction(x) for x in r] for r in M]
    n = len(M); s = Fraction(1)
    for i in range(n):
        piv = next((r for r in range(i, n) if M[r][i] != 0), None)
        if piv is None:
            return Fraction(0)
        if piv != i:
            M[i], M[piv] = M[piv], M[i]; s = -s
        s *= M[i][i]
        for r in range(i + 1, n):
            f = M[r][i] / M[i][i]
            M[r] = [a - f * b for a, b in zip(M[r], M[i])]
    return s

def rank(vecs):
    M = [[Fraction(x) for x in v] for v in vecs]
    r = 0; ncol = len(M[0]) if M else 0
    for c in range(ncol):
        piv = next((i for i in range(r, len(M)) if M[i][c] != 0), None)
        if piv is None:
            continue
        M[r], M[piv] = M[piv], M[r]
        for i in range(len(M)):
            if i != r and M[i][c] != 0:
                f = M[i][c] / M[r][c]
                M[i] = [a - f * b for a, b in zip(M[i], M[r])]
        r += 1
    return r

def dot(a, b):
    return sum(x * y for x, y in zip(a, b))

def normal(pts):
    """Integer normal vector of the hyperplane through d points in R^d (cofactors)."""
    d = len(pts[0]); base = pts[0]
    rows = [[x - y for x, y in zip(p, base)] for p in pts[1:]]
    n = []
    for j in range(d):
        minor = [[r[k] for k in range(d) if k != j] for r in rows]
        n.append(int((-1) ** j * det(minor)) if minor else 1)
    return n

def facets(V):
    d = len(V[0]); F = set()
    for S in combinations(range(len(V)), d):
        n = normal([V[i] for i in S])
        if all(x == 0 for x in n):
            continue
        h = dot(n, V[S[0]]); vals = [dot(n, v) - h for v in V]
        if all(x <= 0 for x in vals) or all(x >= 0 for x in vals):
            F.add(frozenset(i for i in range(len(V)) if vals[i] == 0))
    # keep only genuine facets (affine dimension d-1)
    out = []
    for f in F:
        pts = [V[i] for i in f]
        if rank([[x - y for x, y in zip(p, pts[0])] for p in pts[1:]]) == d - 1:
            out.append(f)
    return out

def graph(V):
    F = facets(V); n = len(V)
    # p is a vertex iff the intersection of the facets containing p is {p}
    verts = {i for i in range(n)
             if any(i in f for f in F) and frozenset.intersection(*[f for f in F if i in f]) == {i}}
    E = set()
    for a, b in combinations(range(n), 2):
        common = [f for f in F if a in f and b in f]
        if common and frozenset.intersection(*common) == {a, b}:
            E.add((a, b))
    return F, verts, E

def ham_path(n, E):
    adj = {i: set() for i in range(n)}
    for a, b in E:
        adj[a].add(b); adj[b].add(a)
    def rec(path, seen):
        if len(path) == n:
            return True
        return any(rec(path + [v], seen | {v}) for v in adj[path[-1]] if v not in seen)
    return any(rec([s], {s}) for s in range(n))

def hamiltonian(n, E):
    adj = {i: set() for i in range(n)}
    for a, b in E:
        adj[a].add(b); adj[b].add(a)
    path = [0]; seen = {0}
    def rec():
        if len(path) == n:
            return 0 in adj[path[-1]]
        for v in sorted(adj[path[-1]]):
            if v not in seen:
                seen.add(v); path.append(v)
                if rec():
                    return True
                seen.remove(v); path.pop()
        return False
    return rec(), list(path)

ok = True
def check(cond, msg):
    global ok
    print(("ok   " if cond else "FAIL ") + msg)
    ok = ok and cond

AX = [(2,0,0),(-2,0,0),(0,2,0),(0,-2,0),(0,0,2),(0,0,-2)]
CUBE = [p for p in product([1,-1], repeat=3)]
RD = AX + CUBE

# ---- rhombic dodecahedron
F, verts, E = graph(RD)
check(len(verts) == 14, "rhombic dodecahedron: all 14 points are vertices")
check(rank([[x - y for x, y in zip(p, RD[0])] for p in RD[1:]]) == 3, "it is 3-dimensional")
check(len(F) == 12 and all(len(f) == 4 for f in F), "12 facets, all quadrilaterals (rhombi)")
check(len(E) == 24, "24 edges")
check(len(RD) - len(E) + len(F) == 2, "Euler: V - E + F = 2")
cubeIdx = set(range(6, 14))
check(all((a in cubeIdx) != (b in cubeIdx) for a, b in E),
      "every edge joins a cube vertex (+-1,+-1,+-1) to an axis vertex: bipartite 8 + 6")
h, _ = hamiltonian(14, E)
check(not h, "exhaustive DFS: no Hamiltonian cycle")
check(not ham_path(14, E), "exhaustive DFS: not even a Hamiltonian path")

# ---- re-check the Lean tables from Main.lean
src = open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'lean4', 'Main.lean')).read()
def table(name):
    i = src.index('def ' + name); i = src.index(':= [', i) + 3
    j = src.index('\n]', i)
    txt = src[i:j + 2].replace('(', '[').replace(')', ']')
    return eval(txt)
edges = table('rdEdges'); nonedges = table('rdNonEdges')
idx = {p: i for i, p in enumerate(RD)}
def T(v): return tuple(v)
Ecalc = {frozenset(e) for e in E}
good = len(edges) == 24
for s, a, c in edges:
    s, a, c = T(s), T(a), T(c)
    others = [r for r in RD if r not in (s, a)]
    good &= frozenset((idx[s], idx[a])) in Ecalc
    good &= dot(c, s) == dot(c, a) and all(dot(c, r) < dot(c, s) for r in others)
check(good, "Lean edge table = facet-computed edges; every exposing functional is valid")
good = len(nonedges) == 67
for p, q, k, cert in nonedges:
    p, q = T(p), T(q)
    good &= frozenset((idx[p], idx[q])) not in Ecalc
    ws = [(m, T(w)) for m, w in cert]
    good &= k > 0 and sum(m for m, _ in ws) == 2 * k
    good &= all(w in RD and w not in (p, q) for _, w in ws)
    good &= all(sum(m * w[j] for m, w in ws) == k * (p[j] + q[j]) for j in range(3))
check(good, "Lean non-edge table: 67 pairs, all non-edges, all certificates valid")
pairs = {frozenset((T(e[0]), T(e[1]))) for e in edges} | {frozenset((T(e[0]), T(e[1]))) for e in nonedges}
check(len(pairs) == 91, "the two tables cover all C(14,2) = 91 pairs")

# ---- pyramid over the rhombic dodecahedron (4-dimensional)
PY = [p + (0,) for p in RD] + [(0, 0, 0, 1)]
F4, verts4, E4 = graph(PY)
check(len(verts4) == 15 and rank([[x - y for x, y in zip(p, PY[0])] for p in PY[1:]]) == 4,
      "pyramid: 15 vertices, 4-dimensional")
check(len(F4) == 13 and len(E4) == 38, "pyramid: 13 facets (base + 12 pyramids over rhombi), 38 edges")
check(not any(a in cubeIdx and b in cubeIdx for a, b in E4), "pyramid: cube vertices pairwise non-adjacent")
h4, _ = hamiltonian(15, E4)
check(not h4, "pyramid: exhaustive DFS finds no Hamiltonian cycle")

# ---- octahedron (sanity: Hamiltonian)
OC = [(1,0,0),(0,1,0),(0,0,1),(-1,0,0),(0,-1,0),(0,0,-1)]
Fo, vo, Eo = graph(OC)
ho, cyc = hamiltonian(6, Eo)
check(len(Fo) == 8 and len(Eo) == 12 and ho, "octahedron: 8 facets, 12 edges, Hamiltonian cycle %s" % cyc)

# ---- an alternative 3-dimensional example: triakis octahedron
TO = [(12,0,0),(-12,0,0),(0,12,0),(0,-12,0),(0,0,12),(0,0,-12)] + \
     [(5*a, 5*b, 5*c) for a, b, c in product([1,-1], repeat=3)]
Ft, vt, Et = graph(TO)
ht, _ = hamiltonian(14, Et)
check(len(vt) == 14 and len(Ft) == 24 and len(Et) == 36 and not ht,
      "triakis octahedron (alternative): 14 vertices, 24 facets, 36 edges, non-Hamiltonian")

check(all(len(f) == 3 for f in Ft), "triakis octahedron: all 24 facets are triangles (simplicial)")

# ---- facet-adjacency (dual) graph of the cuboctahedron
CO = sorted({tuple(p[i] for i in perm) for p in product([1,-1],[1,-1],[0])
             for perm in [(0,1,2),(0,2,1),(1,0,2),(1,2,0),(2,0,1),(2,1,0)]})
Fc, vc, Ec = graph(CO)
Fc = list(Fc)
dualE = {(i, j) for i, j in combinations(range(len(Fc)), 2) if len(Fc[i] & Fc[j]) == 2}
hc, _ = hamiltonian(len(Fc), dualE)
sizes = sorted(len(f) for f in Fc)
check(len(vc) == 12 and len(Ec) == 24 and sizes == [3]*8 + [4]*6,
      "cuboctahedron: 12 vertices, 24 edges, 8 triangles + 6 squares")
check(len(dualE) == 24 and all({len(Fc[i]), len(Fc[j])} == {3, 4} for i, j in dualE) and not hc,
      "cuboctahedron: facet-adjacency graph is bipartite 8 + 6 with 24 edges, non-Hamiltonian")

print("ALL CHECKS PASSED" if ok else "SOME CHECK FAILED")
sys.exit(0 if ok else 1)
