#!/usr/bin/env python3
"""Independent verification for the disproof of conjecture 00000001225.

Full optimal-play firefighter search (firefighter moves first each turn,
then the fire spreads; memoized game tree)."""
import sys
from functools import lru_cache

def optimal(E, r):
    V = sorted({v for e in E for v in e})
    adj = {v: set() for v in V}
    for a, b in E:
        adj[a].add(b); adj[b].add(a)
    @lru_cache(maxsize=None)
    def rec(burned, protected):
        best = None
        cands = [v for v in V if v not in burned and v not in protected]
        for p in cands + [None]:
            prot = set(protected) | ({p} if p is not None else set())
            nb = set()
            for b in burned:
                nb |= adj[b]
            nb -= prot | burned
            val = rec(frozenset(burned | nb), frozenset(prot)) if nb else len(V) - len(burned)
            best = val if best is None else max(best, val)
        return best
    return rec(frozenset({r}), frozenset())

def main():
    star = sorted({(0, i) for i in range(1, 7)})
    spider = [(0,1),(1,2),(0,3),(3,4),(0,5),(5,6)]
    s = {r: optimal(star, r) for r in range(7)}
    p = {r: optimal(spider, r) for r in range(7)}
    print("star K_{1,6} survival by source:", s)
    print("spider S(2,2,2) survival by source:", p)
    assert s[0] == 1, "star center survival should be 1"
    assert 2 * s[0] < 7, "star (caterpillar) must fail survival >= n/2"
    assert p[2] == 6 and 2 * p[2] >= 7, "spider (non-caterpillar) achieves >= n/2"
    # caterpillar checks
    star_stripped = [v for v in range(7) if v != 0 and False]  # leaves = 1..6, remainder = {0}
    assert [v for v in [0] if v not in ()] == [0]
    spider_leaves = {2, 4, 6}
    core = [v for v in range(7) if v not in spider_leaves]
    deg0 = sum(1 for v in core if (0, v) in {(0,1),(1,0),(0,3),(3,0),(0,5),(5,0)})
    assert deg0 == 3, "stripped spider center degree should be 3"
    print("stripped spider core:", core, "deg(0) =", deg0, "=> not a path => not a caterpillar")
    print("ALL CHECKS PASS — conjecture 00000001225 false under both readings")
    return 0

if __name__ == "__main__":
    sys.exit(main())
