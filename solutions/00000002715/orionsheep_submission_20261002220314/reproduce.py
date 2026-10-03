#!/usr/bin/env python3
"""Independent verification for the disproof of conjecture 00000002715.

Builds the boundary of the 4-simplex from scratch (all 5 tetrahedral
facets, full face lattice), verifies:
  1. each vertex link is the boundary of a 3-simplex (f-vector (4,6,4)),
     so dDelta^4 is a closed combinatorial 3-manifold;
  2. EVERY one of the 5! = 120 facet orders satisfies the conjecture's
     own shelling condition ("intersection with previous faces is a pure
     (dim-1) complex": every covered vertex/edge lies in a covered
     triangle);
  3. the vertex count is 5 < 12.
Exit 0 iff all checks pass.
"""
import sys
from itertools import combinations, permutations

def main():
    V = frozenset(range(5))
    facets = [frozenset(c) for c in combinations(V, 4)]          # 5 tetrahedra
    faces = set()                                                # full face lattice
    for f in facets:
        for k in range(1, 5):
            faces.update(frozenset(c) for c in combinations(f, k))
    assert len(facets) == 5

    # (1) vertex links are tetrahedron boundaries: link(v) facets are the
    # 3-subsets tau of V - {v} with tau + {v} a facet; since every 4-subset
    # containing v is a facet, link(v) = boundary of simplex on V - {v}.
    for v in V:
        link_facets = [f - {v} for f in facets if v in f]
        assert sorted(map(sorted, link_facets)) == sorted(
            map(sorted, combinations(V - {v}, 3))), "link facets wrong"
        lv = len({s for t in link_facets for s in combinations(t, 1)})
        le = len({s for t in link_facets for s in combinations(t, 2)})
        lt = len(link_facets)
        assert (lv, le, lt) == (4, 6, 4), f"link f-vector {(lv, le, lt)} != (4,6,4)"
    print("links: all 5 vertex links are tetrahedron boundaries, f-vector (4,6,4)")

    # (2) shelling check under the conjecture's stated definition
    def covered_pure(order, i):
        f = order[i]
        earlier = order[:i]
        def covered(g):  # is face g contained in some earlier facet?
            return any(g <= e for e in earlier)
        tris = [frozenset(t) for t in combinations(f, 3)]
        for v in f:                       # covered vertex in a covered triangle
            if covered(frozenset([v])):
                if not any(covered(t) and v in t for t in tris):
                    return False
        for e in combinations(f, 2):      # covered edge in a covered triangle
            e = frozenset(e)
            if covered(e):
                if not any(covered(t) and e <= t for t in tris):
                    return False
        return True

    n_ok = 0
    for perm in permutations(facets):
        if all(covered_pure(perm, i) for i in range(5)):
            n_ok += 1
    print(f"shelling: {n_ok}/120 facet orders satisfy the stated pure-intersection condition")
    assert n_ok == 120

    # (3) vertex count
    used = set().union(*facets)
    assert used == V and len(used) == 5
    print(f"vertices: dDelta^4 has {len(used)} vertices; conjectured minimum is 12; 5 < 12")
    assert 5 < 12
    print("ALL CHECKS PASS — shellable 3-manifold complex with 5 < 12 vertices")
    return 0

if __name__ == "__main__":
    sys.exit(main())
