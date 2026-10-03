#!/usr/bin/env python3
"""Independent verification for the disproof of conjecture 00000000057.

Builds K_{3,3} and disjoint unions G_k from scratch, then checks:
  1. G_k is 3-regular (minimum degree 3);
  2. G_k is bipartite (BFS 2-coloring);
  3. EVERY simple cycle of K_{3,3} has even length (exhaustive
     enumeration; lengths are exactly {4, 6});
  4. the number of distinct PRIME cycle lengths of G_k is 0
     (k = 1..6), while n = 6k -> infinity and log n / log log n
     diverges.
Exit 0 iff all checks pass.
"""
import sys
from math import log2
from itertools import combinations


def is_prime(n):
    if n < 2:
        return False
    d = 2
    while d * d <= n:
        if n % d == 0:
            return False
        d += 1
    return True


def k33():
    """Adjacency sets of K_{3,3} on vertices 0..5 (0-2 left, 3-5 right)."""
    adj = {v: set() for v in range(6)}
    for a in range(3):
        for b in range(3, 6):
            adj[a].add(b)
            adj[b].add(a)
    return adj


def disjoint_union(adj, k):
    adj_k = {}
    for c in range(k):
        for v, nbrs in adj.items():
            adj_k[6 * c + v] = {6 * c + u for u in nbrs}
    return adj_k


def all_simple_cycles(adj):
    """Enumerate all simple cycles: each cycle found once from its
    smallest vertex (canonical rotation+direction)."""
    cycles = []
    verts = sorted(adj)

    def dfs(start, cur, path, seen):
        for nxt in sorted(adj[cur]):
            if nxt == start and len(path) >= 3:
                cycles.append(tuple(path))
            elif nxt > start and nxt not in seen:
                seen.add(nxt)
                path.append(nxt)
                dfs(start, nxt, path, seen)
                path.pop()
                seen.remove(nxt)

    for s in verts:
        dfs(s, s, [s], {s})
    return cycles


def main():
    adj1 = k33()

    # sanity: K_{3,3} structure
    assert all(len(adj1[v]) == 3 for v in adj1), "K_{3,3} not 3-regular?"
    left = {0, 1, 2}
    for a in left:
        assert adj1[a] == {3, 4, 5}
    print("K_{3,3}: 3-regular, bipartition {0,1,2} | {3,4,5} verified")

    cycles1 = all_simple_cycles(adj1)
    lengths = sorted({len(c) for c in cycles1})
    print(f"K_{{3,3}} simple cycles: {len(cycles1)} total; distinct "
          f"lengths {lengths}")
    assert all(L % 2 == 0 for L in lengths), "odd cycle found in K_{3,3}!"
    assert lengths == [4, 6]

    prime_lengths = sorted(L for L in lengths if is_prime(L))
    print(f"prime cycle lengths of K_{{3,3}}: {prime_lengths} (empty = none)")
    assert prime_lengths == []

    # disjoint unions: min degree, bipartiteness, prime-cycle count
    for k in range(1, 7):
        adjk = disjoint_union(adj1, k)
        n = len(adjk)
        assert all(len(a) == 3 for a in adjk.values()), "not 3-regular"
        color = {}
        for root in adjk:
            if root in color:
                continue
            color[root] = 0
            stack = [root]
            while stack:
                u = stack.pop()
                for v in adjk[u]:
                    if v not in color:
                        color[v] = 1 - color[u]
                        stack.append(v)
                    else:
                        assert color[v] != color[u], "not bipartite!"
        # every cycle lies inside one component: component cycles = K33 cycles
        n_prime_lengths = len(prime_lengths)
        print(f"k={k}: n=6k={n}, min degree 3, bipartite OK, "
              f"distinct prime cycle lengths = {n_prime_lengths}")
        assert n_prime_lengths == 0

    print("divergence anchor: log2(n)/log2(log2(n)) for n = 6k:")
    prev = 0.0
    for k in (1, 2, 4, 8, 16, 32):
        n = 6 * k
        r = log2(n) / log2(log2(n))
        print(f"  n={n:>4}: {r:.3f}")
        assert r > prev or k == 1
        prev = r

    print("ALL CHECKS PASS — G_k has zero prime cycle lengths for all k, "
          "n unbounded")
    return 0


if __name__ == "__main__":
    sys.exit(main())
