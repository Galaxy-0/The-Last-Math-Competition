#!/usr/bin/env python3
"""Standalone reproduction of the disproof of TLMC conjecture 00000001238
(log-concavity of Jacobian invariant factors; equality iff direct sums of cycles).

Run:  python3 reproduce.py
Pure standard library; full run (including the exhaustive sweep over all 32768
graphs on 6 labeled vertices) takes about 15 seconds.

Conventions (stated in the write-up and fixed by the pipeline's own confirmed
instance): the invariant-factor sequence of the Jacobian Jac(G) = Z^n / rows(L^o)
is the nontrivial part (d1 | d2 | ... | dk) of the Smith diagonal of the reduced
Laplacian L^o; "log-concavity" is the system of interior inequalities
d_i^2 >= d_{i-1} * d_{i+1}; "equality" means every interior inequality is an
equality.  Our counterexamples violate/attain these under every alternative
convention as well (see main.tex, Remark 2).
"""
from itertools import combinations
from math import gcd

FAILURES = []

def check(name, cond):
    print(("PASS  " if cond else "FAIL  ") + name)
    if not cond:
        FAILURES.append(name)

# ------------------------------------------------------------ integer linalg -
def matmul(A, B):
    n, k, m = len(A), len(B), len(B[0])
    return [[sum(A[i][t] * B[t][j] for t in range(k)) for j in range(m)] for i in range(n)]

def det(M):
    n = len(M)
    if n == 1:
        return M[0][0]
    if n == 2:
        return M[0][0] * M[1][1] - M[0][1] * M[1][0]
    return sum(((-1) ** j) * M[0][j] * det([row[:j] + row[j + 1:] for row in M[1:]])
               for j in range(n) if M[0][j])

def invariant_factors(L):
    """Nontrivial invariant factors of Z^rows / rows(L) via determinantal
    divisors d_k = gcd of all k x k minors (d_k = s_1*...*s_k)."""
    rows, cols = len(L), len(L[0])
    prev, s = 1, []
    for k in range(1, min(rows, cols) + 1):
        g = 0
        for rs in combinations(range(rows), k):
            for cs in combinations(range(cols), k):
                g = gcd(g, abs(det([[L[i][j] for j in cs] for i in rs])))
        s.append(g // prev if g else 0)
        prev = g
    return [x for x in s if x not in (0, 1)]

# ------------------------------------------------------------ graph machinery -
E6 = list(combinations(range(6), 2))

def edge_idx6(i, j):
    a, b = min(i, j), max(i, j)
    return E6.index((a, b))

def adj_of_mask(mask, n=6):
    a = [[0] * n for _ in range(n)]
    idx = list(combinations(range(n), 2))
    for i, (u, v) in enumerate(idx):
        if mask >> i & 1:
            a[u][v] = a[v][u] = 1
    return a

def adj_from_pairs(pairs, n):
    a = [[0] * n for _ in range(n)]
    for u, v in pairs:
        a[u][v] = a[v][u] = 1
    return a

def connected(a, n):
    seen = {0}
    st = [0]
    while st:
        u = st.pop()
        for v in range(n):
            if a[u][v] and v not in seen:
                seen.add(v)
                st.append(v)
    return len(seen) == n

def lap_minor(a, n, drop=0):
    idx = [i for i in range(n) if i != drop]
    return [[(sum(a[u]) if u == v else -a[u][v]) for v in idx] for u in idx]

def is_cactus(a, n):
    """Connected graph in which every block is a single edge or a cycle
    (Tarjan biconnected components)."""
    if not connected(a, n):
        return False
    import sys
    sys.setrecursionlimit(10000)
    disc = [-1] * n
    low = [0] * n
    parent = [-1] * n
    stack = []
    comps = []
    timer = [0]
    def dfs(u):
        disc[u] = low[u] = timer[0]
        timer[0] += 1
        children = 0
        for v in range(n):
            if a[u][v]:
                if disc[v] == -1:
                    parent[v] = u
                    children += 1
                    stack.append((u, v))
                    dfs(v)
                    low[u] = min(low[u], low[v])
                    if (parent[u] == -1 and children > 1) or (parent[u] != -1 and low[v] >= disc[u]):
                        comp = []
                        while True:
                            e = stack.pop()
                            comp.append(e)
                            if e == (u, v):
                                break
                        comps.append(comp)
                elif v != parent[u] and disc[v] < disc[u]:
                    stack.append((u, v))
                    low[u] = min(low[u], disc[v])
    for i in range(n):
        if disc[i] == -1:
            dfs(i)
            if stack:
                comps.append(list(stack))
                stack.clear()
    for comp in comps:
        vs = set()
        for u, v in comp:
            vs.add(u)
            vs.add(v)
        if len(comp) == 1:
            continue
        if len(comp) != len(vs):
            return False
        deg = {v: 0 for v in vs}
        for u, v in comp:
            deg[u] += 1
            deg[v] += 1
        if any(d != 2 for d in deg.values()):
            return False
    return True

def interior_ok(s):
    return all(s[i] * s[i] >= s[i - 1] * s[i + 1] for i in range(1, len(s) - 1))

def interior_eq(s):
    return all(s[i] * s[i] == s[i - 1] * s[i + 1] for i in range(1, len(s) - 1))

# ============================================================ counterexample A
print("== Counterexample A: K_{2,4} — log-concavity fails ==")
K24_pairs = [(0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (1, 3), (1, 4), (1, 5)]
K24mask = sum(1 << edge_idx6(u, v) for u, v in K24_pairs)   # 510
K24 = adj_from_pairs(K24_pairs, 6)
L24 = [[4, -1, -1, -1, -1], [-1, 2, 0, 0, 0], [-1, 0, 2, 0, 0], [-1, 0, 0, 2, 0], [-1, 0, 0, 0, 2]]
U24 = [[1, 0, 0, 0, 0], [0, 0, 1, 0, 0], [2, 1, 7, 0, 0], [2, 1, 6, 1, 0], [2, 1, 5, 1, 1]]
V24 = [[0, -1, 0, 0, 2], [-1, -4, 1, 0, 1], [0, 0, 0, 0, 1], [0, 0, -1, 1, 1], [0, 0, 0, -1, 5]]
diag11228 = [[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 2, 0, 0], [0, 0, 0, 2, 0], [0, 0, 0, 0, 8]]

check("adjacency mask 510 gives exactly the reduced Laplacian L24", lap_minor(K24, 6) == L24)
check("U24 * L24 * V24 = diag(1,1,2,2,8)", matmul(matmul(U24, L24), V24) == diag11228)
check("det U24 = det V24 = -1 (unimodular)", det(U24) == -1 and det(V24) == -1)
s24 = invariant_factors(L24)
check("invariant factors of Z^5/rows(L24): (2,2,8)", s24 == [2, 2, 8])
check("nontrivial sequence (2,2,8); 2*2=4 < 2*8=16 (interior violation)",
      s24[-3:] == [2, 2, 8] and 2 * 2 < 2 * 8)
check("tau(K_{2,4}) = 32 = 2^(4-1)*4^(2-1) = 1*1*2*2*8",
      det(L24) == 32 and 2 ** 3 * 4 == 32 and 1 * 1 * 2 * 2 * 8 == 32)
check("K_{2,4} is connected and not a cactus (not a direct sum of cycles)",
      connected(K24, 6) and not is_cactus(K24, 6))

# ============================================================ counterexample B
print()
print("== Counterexample B: K4 (and K5) — equality without being a cycle sum ==")
K4_pairs = [(u, v) for u in range(4) for v in range(u + 1, 4)]
K4mask = sum(1 << E6.index((u, v)) for u, v in K4_pairs)    # 615
K4 = adj_from_pairs(K4_pairs, 4)
LK4 = [[3, -1, -1], [-1, 3, -1], [-1, -1, 3]]
U4 = [[1, 0, 0], [3, 1, 0], [2, 1, 1]]
V4 = [[0, 0, 1], [-1, 1, 1], [0, -1, 2]]
diag144 = [[1, 0, 0], [0, 4, 0], [0, 0, 4]]

check("adjacency mask 615 gives exactly the reduced Laplacian LK4", lap_minor(K4, 4) == LK4)
check("U4 * LK4 * V4 = diag(1,4,4)", matmul(matmul(U4, LK4), V4) == diag144)
check("det U4 = det V4 = 1 (unimodular)", det(U4) == 1 and det(V4) == 1)
s4 = invariant_factors(LK4)
check("invariant factors (4,4) with equality 4*4 = 4*4",
      s4 == [4, 4] and 4 * 4 == 4 * 4)
check("tau(K4) = 16 = 4^(4-2)", det(LK4) == 16 and 4 ** 2 == 16)
triA = (1 << E6.index((0, 1))) | (1 << E6.index((1, 2))) | (1 << E6.index((0, 2)))
triB = (1 << E6.index((0, 1))) | (1 << E6.index((1, 3))) | (1 << E6.index((0, 3)))
check("edge {0,1} of K4 lies on two distinct triangles {0,1,2} and {0,1,3}",
      all(K4[u][v] for t in ((0, 1, 2), (0, 1, 3)) for u, v in combinations(t, 2))
      and triA != triB)

n_cacti4, max_edges_cactus4, taus_cactus4 = 0, 0, set()
E4 = list(combinations(range(4), 2))
for mask in range(1 << 6):
    a4 = [[0] * 4 for _ in range(4)]
    for i, (u, v) in enumerate(E4):
        if mask >> i & 1:
            a4[u][v] = a4[v][u] = 1
    if connected(a4, 4) and is_cactus(a4, 4):
        n_cacti4 += 1
        max_edges_cactus4 = max(max_edges_cactus4, sum(a4[u][v] for u in range(4) for v in range(u + 1, 4)))
        taus_cactus4.add(det(lap_minor(a4, 4)))
check("all 31 connected cacti on 4 vertices have <= 4 edges and tau in {1,3,4}; "
      "K4 has 6 edges and tau=16, hence K4 is not a direct sum of cycles",
      n_cacti4 == 31 and max_edges_cactus4 <= 4 and taus_cactus4 <= {1, 3, 4})

K5 = adj_from_pairs([(u, v) for u in range(5) for v in range(u + 1, 5)], 5)
s5 = invariant_factors(lap_minor(K5, 5))
check("K5: invariant factors (5,5,5), all interior equalities 25=25, tau=125, not a cactus",
      s5 == [5, 5, 5] and interior_eq([5, 5, 5]) and det(lap_minor(K5, 5)) == 125
      and not is_cactus(K5, 5))

# ===================================================== internal incoherence ==
print()
print("== Remark: the conjecture's own equality class violates log-concavity ==")
w_pairs = [(0, 1), (1, 2), (0, 2), (2, 3), (3, 4), (2, 4),
           (2, 5), (5, 6), (6, 7), (7, 8), (8, 9), (9, 2)]
w = adj_from_pairs(w_pairs, 10)
sW = invariant_factors(lap_minor(w, 10))
check("C3 v C3 v C6 IS a direct sum of cycles (cactus), yet has invariant factors "
      "(3,3,6) with 3*3=9 < 3*6=18: not log-concave",
      is_cactus(w, 10) and sW == [3, 3, 6] and 3 * 3 < 3 * 6)

# ================================================= exhaustive 6-vertex sweep =
print()
print("== Exhaustive sweep: all 2^15 graphs on 6 labeled vertices ==")
conn = viol = torsion2248 = eq_nc = eq3_nc = 0
k24_in_2248 = k6_in_eq3 = False
K6mask = (1 << 15) - 1
for mask in range(1 << 15):
    a = adj_of_mask(mask, 6)
    if not connected(a, 6):
        continue
    conn += 1
    s = invariant_factors(lap_minor(a, 6))
    if len(s) >= 2:
        if not interior_ok(s):
            viol += 1
        if interior_eq(s) and not is_cactus(a, 6):
            eq_nc += 1
            if len(s) >= 3:
                eq3_nc += 1
                if mask == K6mask:
                    k6_in_eq3 = True
    if s[-3:] == [2, 2, 8]:
        torsion2248 += 1
        if mask == K24mask:
            k24_in_2248 = True

check("connected 6-vertex graphs: 26704", conn == 26704)
check("interior log-concavity violations (nontrivial seq length >= 2): 75", viol == 75)
check("graphs with torsion exactly Z2 x Z2 x Z8: 15, and K_{2,4} (mask 510) is one of them",
      torsion2248 == 15 and k24_in_2248)
check("equality-but-not-cactus graphs: 3793; of which 31 have sequences of length >= 3 "
      "(K6, with (6,6,6,6), is one)", eq_nc == 3793 and eq3_nc == 31 and k6_in_eq3)

# ============================================================================ =
print()
if FAILURES:
    print("FAILED:", FAILURES)
    raise SystemExit(1)
print("ALL CHECKS PASSED")
