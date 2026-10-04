#!/usr/bin/env python3
"""Independent check for the disproof of conjecture 00000001289 (Python 3, standard library).

Claim: the "nim graph" Q_xor(n) of the hypercube (2^n vertices) has diameter 2^n - 1 and
chromatic number 2^n.  This script uses a different method from the Lean proof: brute-force
enumeration of all labelled graphs, breadth-first search for distances, and exhaustive or
backtracking search for colourings.
"""
import itertools
import sys

INF = float("inf")


def bfs_dist(N, adj, s):
    d = [INF] * N
    d[s] = 0
    q = [s]
    for x in q:
        for y in adj[x]:
            if d[y] == INF:
                d[y] = d[x] + 1
                q.append(y)
    return d


def diameter(N, adj):
    return max(max(bfs_dist(N, adj, s)) for s in range(N))


def colorable(N, adj, k):
    """Backtracking search for a proper k-colouring."""
    col = [-1] * N

    def go(i):
        if i == N:
            return True
        for c in range(k):
            if all(col[j] != c for j in adj[i] if j < i):
                col[i] = c
                if go(i + 1):
                    return True
        col[i] = -1
        return False

    return go(0)


def chromatic(N, adj):
    k = 0
    while not colorable(N, adj, k):
        k += 1
    return k


def adj_from_edges(N, edges):
    adj = [set() for _ in range(N)]
    for a, b in edges:
        adj[a].add(b)
        adj[b].add(a)
    return adj


def all_graphs(N):
    pairs = list(itertools.combinations(range(N), 2))
    for m in range(1 << len(pairs)):
        E = [pairs[i] for i in range(len(pairs)) if m >> i & 1]
        yield E, adj_from_edges(N, E)


ok = True


def check(cond, msg):
    global ok
    print(("OK   " if cond else "FAIL ") + msg)
    ok = ok and cond


# 1. Brute force for n = 2 (N = 4): every one of the 64 labelled graphs.
N = 4
bad = []
stats = {}
for E, adj in all_graphs(N):
    chi, dm = chromatic(N, adj), diameter(N, adj)
    stats[(chi, dm)] = stats.get((chi, dm), 0) + 1
    if chi == 4 and dm == 3:
        bad.append(E)
print("N=4: (chi, diam) -> number of labelled graphs:",
      {str(k): v for k, v in sorted(stats.items(), key=str)})
check(len(bad) == 0, "no graph on 4 vertices has chi = 4 and diam = 3 (64 graphs)")
check(stats.get((4, 1)) == 1, "the only graph with chi = 4 on 4 vertices is K4, with diam 1")

# 2. The general lemma chi = N => complete, and the stronger bound chi + diam <= N + 1,
#    for every labelled graph on N = 3..6 vertices.
for N in range(3, 7):
    full = N * (N - 1) // 2
    lemma = True
    bound = True
    cnt = 0
    for E, adj in all_graphs(N):
        cnt += 1
        chi = chromatic(N, adj)
        if chi == N and len(E) != full:
            lemma = False
        dm = diameter(N, adj)
        if dm != INF and chi + dm > N + 1:
            bound = False
    check(lemma, f"N={N}: chi = N only for the complete graph ({cnt} graphs)")
    check(bound, f"N={N}: chi + diam <= N + 1 for every connected graph")
# In particular no graph on 5 = 2^2 + 1 vertices has chi = 4 and diam = 3 (4 + 3 > 6).


# 3. Concrete readings of Q_xor(n) on vertex set {0, ..., 2^n - 1}.
def cayley(n, S):
    N = 1 << n
    return N, [set(u ^ s for s in S) for u in range(N)]


for n in range(1, 6):
    N = 1 << n
    Nh, adjh = cayley(n, [1 << i for i in range(n)])          # hypercube: u xor v = 2^i
    Nk, adjk = cayley(n, list(range(1, N)))                    # complete: u xor v != 0
    ch, dh = chromatic(Nh, adjh), diameter(Nh, adjh)
    if n <= 3:
        ck = chromatic(Nk, adjk)
    else:  # complete graph (checked): N pairwise adjacent vertices need N colours (pigeonhole)
        ck = N if all(adjk[u] == set(range(N)) - {u} for u in range(N)) else None
    dk = diameter(Nk, adjk)
    claim = (N - 1, N)
    print(f"n={n}: hypercube chi={ch} diam={dh}; complete chi={ck} diam={dk}; claim diam={claim[0]} chi={claim[1]}")
    check(ch == 2 and dh == n, f"n={n}: hypercube reading has chi = 2, diam = n")
    check(ck == N and dk == 1, f"n={n}: complete reading has chi = 2^n, diam = 1")
    if n >= 2:
        check((dh, ch) != claim and (dk, ck) != claim, f"n={n}: both readings violate the claim")

# Every Cayley graph of (Z/2)^n (n = 2, 3) for every nonempty generator set S.
for n in (2, 3):
    N = 1 << n
    found = []
    tot = 0
    for r in range(1, N):
        for S in itertools.combinations(range(1, N), r):
            tot += 1
            Nn, adj = cayley(n, S)
            if diameter(Nn, adj) == N - 1 and chromatic(Nn, adj) == N:
                found.append(S)
    check(not found, f"n={n}: none of the {tot} Cayley graphs Cay((Z/2)^{n}, S) satisfies the claim")

# 4. Directed remark (N = 4): loopless digraphs whose underlying graph has chi = 4 (= K4).
pairs = list(itertools.combinations(range(4), 2))
diam3 = []
acyc = 0
acyclic_ok = True
for states in itertools.product(range(3), repeat=6):   # 0: a->b, 1: b->a, 2: both
    out = [set() for _ in range(4)]
    for (a, b), s in zip(pairs, states):
        if s in (0, 2):
            out[a].add(b)
        if s in (1, 2):
            out[b].add(a)
    dm = max(max(bfs_dist(4, out, s)) for s in range(4))
    # acyclic iff no directed cycle: check via reachability back to itself
    cyc = any(x in out[y] and bfs_dist(4, out, x)[y] < INF for x in range(4) for y in range(4))
    if not cyc:
        acyc += 1
        if dm != INF:
            acyclic_ok = False
    if dm == 3:
        diam3.append(states)
symmetric_ok = all(any(s != 2 for s in st) for st in diam3)
print(f"directed N=4: {len(diam3)} non-symmetric orientations/digraphs over K4 reach directed diameter 3;"
      f" {acyc} acyclic ones (all of infinite diameter)")
check(acyclic_ok and acyc == 24, "the 24 acyclic orientations of K4 all have infinite directed diameter")
check(symmetric_ok, "every digraph over K4 with directed diameter 3 is non-symmetric (impossible for a rule"
      " depending on u xor v = v xor u)")

print("ALL CHECKS PASSED" if ok else "SOME CHECK FAILED")
sys.exit(0 if ok else 1)
