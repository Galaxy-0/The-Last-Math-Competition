#!/usr/bin/env python3
"""
Independent recomputation for the disproof of TLMC conjecture 00000000057.

Conjecture (00000000057): Every n-vertex graph of minimum degree at least 3
contains Omega(log n / log log n) cycles of pairwise distinct prime lengths.

Counterexample family: G_k = disjoint union of k copies of K_{3,3}.
  - n = 6k vertices, minimum degree exactly 3.
  - K_{3,3} is bipartite with parts of size 3: every cycle alternates between
    the parts, hence has even length 2m with m <= 3; a simple cycle has
    m >= 2 (no multi-edges), so all cycle lengths lie in {4, 6}.
  - 4 = 2*2 and 6 = 2*3 are composite, so the number of DISTINCT PRIME
    cycle lengths is 0 for every k, while log n / log log n -> infinity.

This script brute-force enumerates ALL simple cycles of G_k for several k
(no assumptions beyond the adjacency definition) and verifies the attack.
Run:  python3 reproduce.py
"""

import math
import sys
from collections import Counter
from itertools import product

PRIMES = set()


def sieve(limit):
    is_p = [True] * (limit + 1)
    is_p[0] = is_p[1] = False
    for i in range(2, int(limit**0.5) + 1):
        if is_p[i]:
            for j in range(i * i, limit + 1, i):
                is_p[j] = False
    return {i for i in range(limit + 1) if is_p[i]}


PRIMES = sieve(1000)


def build_G(k):
    """Adjacency (as dict of sets) of the disjoint union of k copies of K_{3,3}.

    Vertices 0..6k-1; vertex v lives in block v//6 and side (v%6)<3 (side A)
    or (v%6)>=3 (side B); complete bipartite inside each block only.
    """
    adj = {v: set() for v in range(6 * k)}
    for v in range(6 * k):
        for w in range(6 * k):
            if v < w and v // 6 == w // 6 and ((v % 6 < 3) != (w % 6 < 3)):
                adj[v].add(w)
                adj[w].add(v)
    return adj


def all_simple_cycles(adj):
    """Brute-force enumeration of ALL simple cycles (undirected, up to
    rotation and reflection) via DFS from the smallest vertex of each cycle."""
    verts = sorted(adj)
    cycles = []

    def dfs(start, cur, visited, path):
        for w in sorted(adj[cur]):
            if w == start and len(path) >= 3:
                cycles.append(list(path))
            elif w not in visited and w > start:
                visited.add(w)
                path.append(w)
                dfs(start, w, visited, path)
                path.pop()
                visited.discard(w)

    for s in verts:
        dfs(s, s, {s}, [s])
    return cycles


def check_min_degree(adj, k, need=3):
    N = 6 * k
    for v in range(N):
        deg = len(adj[v])
        assert deg == need, f"vertex {v} has degree {deg}, expected {need}"
        assert all(0 <= w < N for w in adj[v])
    return need


def main():
    print("Conjecture 00000000057: min degree >= 3  =>  Omega(log n / log log n)")
    print("distinct prime cycle lengths.")
    print()
    print("Counterexample family G_k = K_{3,3} + ... + K_{3,3} (k copies), n = 6k.")
    print()

    for k in (1, 2, 3, 5, 8):
        adj = build_G(k)
        n = 6 * k
        deg = check_min_degree(adj, k)

        cyc = all_simple_cycles(adj)
        lens = Counter(len(c) for c in cyc)
        distinct = sorted(lens)
        prime_lens = sorted(L for L in distinct if L in PRIMES)

        # sanity: independently verify each enumerated cycle really is a cycle
        for c in cyc:
            for i in range(len(c)):
                assert c[(i + 1) % len(c)] in adj[c[i]], "bad edge in enumeration"
            assert len(set(c)) == len(c), "repeated vertex"

        logratio = math.log(n) / math.log(math.log(n)) if n > 2 else float("nan")
        print(f"k={k}: n={n}, min degree={deg}, total cycles={len(cyc)}, "
              f"length multiset={dict(sorted(lens.items()))}")
        print(f"      distinct cycle lengths={distinct}, distinct PRIME lengths={prime_lens}, "
              f"count={len(prime_lens)}")
        print(f"      log n / log log n = {logratio:.4f}   "
              f"-> {len(prime_lens)} >= c*{logratio:.4f} for c>0 ? "
              f"{'YES' if len(prime_lens) >= logratio else 'NO'}")
        assert distinct == [4, 6], f"unexpected cycle lengths {distinct}"
        assert prime_lens == [], "unexpected prime cycle length!"
        print()

    print("Verified: for every k, all cycle lengths of G_k are exactly {4, 6},")
    print("both composite, so the number of distinct prime cycle lengths is 0,")
    print("while log n / log log n -> infinity as n = 6k -> infinity.")
    print()
    print("Conclusion: conjecture 00000000057 is FALSE.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
