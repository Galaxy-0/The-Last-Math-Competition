#!/usr/bin/env python3
"""Independent check (Python 3 standard library only) for the disproof of conjecture 00000003952.

Clause refuted: "the graphs of twin-width at most 1 are exactly the distance-hereditary graphs".

  * house H (complement of the path 0-1-2-3-4): twin-width exactly 1, not distance-hereditary;
  * net N (triangle 0,1,2 with pendants 3,4,5): distance-hereditary, twin-width exactly 2.

Methods (different from the Lean proof where possible):
  1. trigraph simulation of the explicit contraction sequence (black/red/none colours);
  2. exact twin-width by exhaustive search over PARTITION sequences (red edge between two
     parts iff the pair is not homogeneous), with memoisation;
  3. distance-hereditary tested three ways: BFS distances in every connected induced
     subgraph; the Bandelt-Mulder pruning characterisation (repeatedly delete a pendant
     vertex or one of a pair of twins); and the forbidden induced subgraphs house, hole
     (C_k, k >= 5), domino, gem;
  4. an enumeration of all connected graphs with at most 6 vertices (nauty-geng if
     installed, otherwise all labelled graphs with at most 5 vertices).
"""
import itertools, shutil, subprocess, sys
from functools import lru_cache

def graph(n, edges):
    adj = [set() for _ in range(n)]
    for a, b in edges:
        adj[a].add(b); adj[b].add(a)
    return n, [frozenset(s) for s in adj]

HOUSE = graph(5, [(0,2),(0,3),(0,4),(1,3),(1,4),(2,4)])
NET   = graph(6, [(0,1),(1,2),(0,2),(0,3),(1,4),(2,5)])
P5    = graph(5, [(0,1),(1,2),(2,3),(3,4)])

# ---------------------------------------------------------------- 1. trigraph simulation
NONE, BLACK, RED = 0, 1, 2
def trigraph(G):
    n, adj = G
    col = {}
    for a in range(n):
        for b in range(n):
            if a != b: col[(a, b)] = BLACK if b in adj[a] else NONE
    return list(range(n)), col

def contract(T, u, v):
    verts, col = T
    assert u in verts and v in verts and u != v
    nv = [w for w in verts if w != v]
    nc = {}
    for a in nv:
        for b in nv:
            if a == b: continue
            if a != u and b != u:
                nc[(a, b)] = col[(a, b)]
            else:
                w = b if a == u else a
                cu, cv = col[(u, w)], col[(v, w)]
                c = BLACK if (cu, cv) == (BLACK, BLACK) else NONE if (cu, cv) == (NONE, NONE) else RED
                nc[(a, b)] = c
    return nv, nc

def max_red(T):
    verts, col = T
    return max((sum(1 for w in verts if w != x and col[(x, w)] == RED) for x in verts), default=0)

def seq_widths(G, seq):
    T = trigraph(G); ws = [max_red(T)]
    for u, v in seq:
        T = contract(T, u, v); ws.append(max_red(T))
    assert len(T[0]) == 1
    return ws

# ---------------------------------------------------------------- 2. exact twin-width
def twin_width(G):
    n, adj = G
    def red(P, Q):
        e = sum(1 for a in P for b in Q if b in adj[a])
        return 0 < e < len(P) * len(Q)
    def width(parts):
        return max((sum(1 for Q in parts if Q is not P and red(P, Q)) for P in parts), default=0)
    @lru_cache(None)
    def best(parts):          # min over completions of the max red degree still to come
        if len(parts) == 1: return 0
        ps = list(parts); res = n
        for i, j in itertools.combinations(range(len(ps)), 2):
            new = [p for k, p in enumerate(ps) if k not in (i, j)] + [ps[i] | ps[j]]
            w = width(new)
            if w >= res: continue
            res = min(res, max(w, best(frozenset(new))))
        return res
    return best(frozenset(frozenset([v]) for v in range(n)))

def first_contraction_min_width(G):
    n, _ = G
    T = trigraph(G)
    return min(max_red(contract(T, u, v)) for u in range(n) for v in range(n) if u != v)

# ---------------------------------------------------------------- 3. distance-hereditary
def bfs(adj, S, s):
    d = {s: 0}; fr = [s]
    while fr:
        nf = []
        for x in fr:
            for y in adj[x]:
                if y in S and y not in d:
                    d[y] = d[x] + 1; nf.append(y)
        fr = nf
    return d

def dh_bfs(G):
    """every connected induced subgraph is isometric; returns (True, None) or (False, witness)"""
    n, adj = G
    V = set(range(n)); full = {x: bfs(adj, V, x) for x in V}
    for r in range(1, n + 1):
        for S in itertools.combinations(range(n), r):
            S = set(S); x0 = min(S)
            if len(bfs(adj, S, x0)) != len(S): continue          # not connected
            for x in S:
                dS = bfs(adj, S, x)
                for y in S:
                    if dS[y] != full[x][y]:
                        return False, (sorted(S), x, y, full[x][y], dS[y])
    return True, None

def dh_pruning(G):
    """Bandelt-Mulder: DH iff reducible to one vertex by deleting pendant vertices and twins"""
    n, adj = G
    S = set(range(n))
    def comps(S):
        seen, k = set(), 0
        for s in S:
            if s not in seen: seen |= set(bfs(adj, S, s)); k += 1
        return k
    # the characterisation is for connected graphs; apply it to each component
    if comps(S) > 1:
        return all(dh_pruning(induced(G, sorted(bfs(adj, S, s)))) for s in S)
    while len(S) > 1:
        for v in sorted(S):
            Nv = adj[v] & S
            if len(Nv) == 1: S.remove(v); break
            if any((adj[w] & S) - {v} == Nv - {w} for w in S if w != v): S.remove(v); break
        else:
            return False
    return True

def induced(G, vs):
    n, adj = G
    idx = {v: i for i, v in enumerate(vs)}
    return len(vs), [frozenset(idx[w] for w in adj[v] if w in idx) for v in vs]

def isomorphic(G, H):
    (n, a), (m, b) = G, H
    if n != m or sorted(map(len, a)) != sorted(map(len, b)): return False
    return any(all((p[y] in b[p[x]]) == (y in a[x]) for x in range(n) for y in range(n))
               for p in itertools.permutations(range(n)))

def cycle(k): return graph(k, [(i, (i + 1) % k) for i in range(k)])
DOMINO = graph(6, [(0,1),(1,2),(3,4),(4,5),(0,3),(1,4),(2,5)])
GEM    = graph(5, [(0,1),(1,2),(2,3),(4,0),(4,1),(4,2),(4,3)])
def dh_forbidden(G):
    n, _ = G
    forb = [HOUSE, DOMINO, GEM] + [cycle(k) for k in range(5, n + 1)]
    for F in forb:
        for vs in itertools.combinations(range(n), F[0]):
            if isomorphic(induced(G, list(vs)), F): return False
    return True

def is_dh(G):
    a, _ = dh_bfs(G); b = dh_pruning(G); c = dh_forbidden(G)
    assert a == b == c, (G, a, b, c)
    return a

# ---------------------------------------------------------------- run
def main():
    ok = True
    def check(cond, msg):
        nonlocal ok
        print(("ok   " if cond else "FAIL ") + msg); ok &= bool(cond)

    # house
    ws = seq_widths(HOUSE, [(3,4), (3,2), (3,1), (3,0)])
    check(ws == [0, 1, 1, 1, 0], f"house: sequence {{3,4}},2,1,0 has red degrees {ws}")
    check(first_contraction_min_width(HOUSE) >= 1, "house: every first contraction creates a red edge (no twins)")
    check(twin_width(HOUSE) == 1, f"house: exact twin-width (partition search) = {twin_width(HOUSE)}")
    dh, wit = dh_bfs(HOUSE)
    check(not dh, f"house: not distance-hereditary, witness (S, x, y, d_G, d_G[S]) = {wit}")
    S = {1, 2, 3, 4}
    check(len(bfs(HOUSE[1], S, 1)) == 4 and bfs(HOUSE[1], set(range(5)), 2)[3] == 2
          and bfs(HOUSE[1], S, 2)[3] == 3, "house: H-0 connected, d_H(2,3)=2, d_{H-0}(2,3)=3")
    print("     Lean/report witness: S = [1, 2, 3, 4], x = 2, y = 3, d_G = 2, d_G[S] = 3")
    check(not dh_pruning(HOUSE) and not dh_forbidden(HOUSE), "house: not DH by pruning and by forbidden subgraphs")
    comp = graph(5, [(a, b) for a in range(5) for b in range(a+1, 5) if b not in HOUSE[1][a]])
    check(isomorphic(comp, P5), "house: complement is the path P5")

    # net
    check(first_contraction_min_width(NET) == 2, "net: every first contraction creates red degree >= 2")
    check(twin_width(NET) == 2, f"net: exact twin-width (partition search) = {twin_width(NET)}")
    ws = seq_widths(NET, [(0,3), (1,4), (2,5), (0,1), (0,2)])
    check(max(ws) == 2, f"net: explicit width-2 sequence, red degrees {ws}")
    # asteroidal triple 3,4,5 (second reason: tww<=1 graphs are permutation graphs, which are AT-free)
    def at_path(G, a, b, c):
        S = set(range(G[0])) - (G[1][c] | {c})
        return b in bfs(G[1], S, a)
    check(all(at_path(NET, a, b, c) for a, b, c in [(3,4,5), (3,5,4), (4,5,3)]),
          "net: 3,4,5 is an asteroidal triple, so the net is not a permutation graph")
    check(is_dh(NET), "net: distance-hereditary (BFS on all 63 induced subgraphs, pruning, forbidden subgraphs)")

    # sanity: P5 agrees with the conjecture
    check(twin_width(P5) == 1 and is_dh(P5), "P5: twin-width 1 and distance-hereditary (sanity)")

    # enumeration
    geng = shutil.which("nauty-geng") or shutil.which("geng")
    if geng:
        print("enumerating connected graphs with nauty-geng (n <= 6):")
        for n in range(1, 7):
            out = subprocess.run([geng, "-q", "-c", str(n)], capture_output=True, text=True).stdout.split()
            a = b = 0; ex1 = ex2 = None
            for g6 in out:
                G = parse_g6(g6); t = twin_width(G); d = is_dh(G)
                if t <= 1 and not d:
                    a += 1; ex1 = ex1 or g6
                    if n == 5:
                        name = "house" if isomorphic(G, HOUSE) else "gem" if isomorphic(G, GEM) else "?"
                        print(f"    n=5, tww<=1, not DH: {g6} = {name}")
                if d and t > 1:
                    b += 1; ex2 = ex2 or g6
                    print(f"    DH, tww={t}: {g6}" + (" = net" if isomorphic(G, NET) else ""))
            print(f"  n={n}: {len(out)} graphs; tww<=1 but not DH: {a} (e.g. {ex1}); DH but tww>1: {b} (e.g. {ex2})")
    else:
        print("nauty-geng not found: enumerating all labelled graphs with n <= 5")
        for n in range(1, 6):
            pairs = list(itertools.combinations(range(n), 2)); a = b = 0
            for mask in range(1 << len(pairs)):
                G = graph(n, [p for i, p in enumerate(pairs) if mask >> i & 1])
                if len(bfs(G[1], set(range(n)), 0)) != n: continue
                t = twin_width(G); d = is_dh(G)
                a += (t <= 1 and not d); b += (d and t > 1)
            print(f"  n={n}: labelled connected graphs with tww<=1 not DH: {a}; DH with tww>1: {b}")
    print("ALL CHECKS PASSED" if ok else "SOME CHECK FAILED")
    sys.exit(0 if ok else 1)

def parse_g6(s):
    n = ord(s[0]) - 63; bits = []
    for ch in s[1:]:
        v = ord(ch) - 63
        bits += [(v >> k) & 1 for k in range(5, -1, -1)]
    edges = []; i = 0
    for j in range(1, n):
        for k in range(j):
            if bits[i]: edges.append((k, j))
            i += 1
    return graph(n, edges)

if __name__ == "__main__":
    main()
