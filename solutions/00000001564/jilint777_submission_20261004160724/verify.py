"""Independent checks for conjecture 00000001564 (Python 3 standard library only).

Claim refuted: "the minimal number of vertices of a k-dimensional cs-neighborly
polytope is 2^(k+1)".  Counterexample: the k-dimensional cross-polytope
conv{+-e_1, ..., +-e_k}, which has 2k < 2^(k+1) vertices.

The Lean proof checks, for k = 1..4, that each subset S of vertices without an
antipodal pair is exactly the set of maximizers of the functional sum(S).
Here we use a different method: for k = 1..5 we enumerate ALL functionals c in
{-1,0,1}^k \\ {0} (and, for k <= 3, all c in {-2..2}^k \\ {0}), compute the set
of maximizers of each, and check that the resulting family of exposed vertex
sets is exactly the family of nonempty antipodal-free vertex subsets (no more,
no less).  The dimension is computed as an exact rank (Fractions).

Further checks:
  * the statement's own "definition" (support point in every direction) holds
    for every finite point set (random functionals, sanity);
  * lower bound: every full-dimensional centrally symmetric polytope whose
    vertices lie in {-1,0,1}^k (k = 2, 3; all 2^4 resp. 2^13 symmetric point sets)
    has at least 2k vertices, so the true minimum 2k is attained by the
    cross-polytope (vertices are found by functional search, which can only
    undercount, so the check is sound);
  * Hanner polytopes built as explicit point sets (all product / free-sum trees,
    dimension <= 6): vertex numbers v satisfy 2d <= v <= 2^d, never 2^(d+1).
"""

import itertools
import random
from fractions import Fraction


def dot(c, p):
    return sum(a * b for a, b in zip(c, p))


def neg(p):
    return tuple(-x for x in p)


def cross(k):
    pts = []
    for i in range(k):
        for s in (1, -1):
            v = [0] * k
            v[i] = s
            pts.append(tuple(v))
    return pts


def rank(vectors):
    m = [[Fraction(x) for x in v] for v in vectors]
    r = 0
    cols = len(m[0]) if m else 0
    for col in range(cols):
        piv = next((i for i in range(r, len(m)) if m[i][col] != 0), None)
        if piv is None:
            continue
        m[r], m[piv] = m[piv], m[r]
        for i in range(len(m)):
            if i != r and m[i][col] != 0:
                f = m[i][col] / m[r][col]
                m[i] = [a - f * b for a, b in zip(m[i], m[r])]
        r += 1
    return r


def affine_dim(pts):
    a = pts[0]
    return rank([[x - y for x, y in zip(p, a)] for p in pts[1:]]) if len(pts) > 1 else 0


def argmax(pts, c):
    vals = [dot(c, p) for p in pts]
    m = max(vals)
    return frozenset(p for p, v in zip(pts, vals) if v == m)


def check_cross(k, coeffs):
    V = cross(k)
    assert len(V) == 2 * k == len(set(V))
    assert all(neg(v) in V for v in V), "central symmetry"
    assert affine_dim(V) == k, "dimension"
    exposed = set()
    for c in itertools.product(coeffs, repeat=k):
        if any(c):
            exposed.add(argmax(V, c))
    # vertices: singletons among exposed sets
    verts = {next(iter(S)) for S in exposed if len(S) == 1}
    assert verts == set(V), "every listed point is a vertex"
    wanted = set()
    for r in range(1, len(V) + 1):
        for S in itertools.combinations(V, r):
            if all(neg(u) not in S for u in S):
                wanted.add(frozenset(S))
    assert exposed == wanted, "exposed sets = antipodal-free subsets"
    return len(V), len(wanted)


def support_points_sanity():
    rnd = random.Random(1564)
    for _ in range(200):
        k = rnd.randint(1, 4)
        pts = [tuple(rnd.randint(-3, 3) for _ in range(k)) for _ in range(rnd.randint(1, 8))]
        c = tuple(rnd.randint(-5, 5) for _ in range(k))
        best = max(pts, key=lambda p: dot(c, p))
        assert all(dot(c, q) <= dot(c, best) for q in pts)


def lower_bound_small(k):
    """All centrally symmetric point sets in {-1,0,1}^k \\ {0}; for the full-dimensional
    ones, the number of exposed points found by search is >= 2k."""
    pts = [p for p in itertools.product((-1, 0, 1), repeat=k) if any(p)]
    reps = [p for p in pts if p > neg(p)]
    funcs = [c for c in itertools.product(range(-3, 4), repeat=k) if any(c)]
    table = {c: {p: dot(c, p) for p in pts} for c in funcs}
    best = None
    count = 0
    for mask in range(1, 1 << len(reps)):
        P = []
        for i, p in enumerate(reps):
            if mask >> i & 1:
                P += [p, neg(p)]
        if rank(P) < k:
            continue
        count += 1
        found = set()
        for c in funcs:
            t = table[c]
            m = max(t[p] for p in P)
            arg = [p for p in P if t[p] == m]
            if len(arg) == 1:
                found.add(arg[0])
        assert len(found) >= 2 * k, (P, found)
        assert all(neg(v) in found for v in found)
        best = len(found) if best is None else min(best, len(found))
    return count, best


def hanner_counts(maxd):
    """Explicit Hanner polytopes (as vertex sets) up to dimension maxd."""
    H = {1: {frozenset({(1,), (-1,)})}}
    for d in range(2, maxd + 1):
        H[d] = set()
        for d1 in range(1, d):
            d2 = d - d1
            for A in H[d1]:
                for B in H[d2]:
                    prod = frozenset(a + b for a in A for b in B)
                    fsum = frozenset([a + (0,) * d2 for a in A] + [(0,) * d1 + b for b in B])
                    H[d].add(prod)
                    H[d].add(fsum)
    result = {}
    for d, polys in H.items():
        vs = set()
        for P in polys:
            P = list(P)
            # each point is a vertex: c = v is uniquely maximized at v
            for v in P:
                assert all(dot(v, q) < dot(v, v) for q in P if q != v)
            assert affine_dim(P) == d
            assert all(neg(v) in P for v in P)
            vs.add(len(P))
        result[d] = (len(polys), sorted(vs))
    return result


def main():
    print("== cross-polytopes")
    for k in range(1, 6):
        n, f = check_cross(k, (-1, 0, 1))
        print(f"k={k}: dim {k}, cs, {n} = 2k vertices; the exposed vertex sets for c in "
              f"{{-1,0,1}}^k are exactly the {f} antipodal-free subsets; "
              f"2k = {2*k} < 2^(k+1) = {2**(k+1)}: {2*k < 2**(k+1)}")
        assert 2 * k < 2 ** (k + 1)
    for k in range(1, 4):
        check_cross(k, range(-2, 3))
        print(f"k={k}: same family of exposed sets for all c in {{-2..2}}^k")
    support_points_sanity()
    print("support point in every direction: OK (random sanity)")
    print("== lower bound 2k (cs point sets in {-1,0,1}^k)")
    for k in (2, 3):
        cnt, best = lower_bound_small(k)
        print(f"k={k}: {cnt} full-dimensional cs point sets; each spans a polytope with at least "
              f"{best} = 2k vertices (found by functional search)")
        assert best == 2 * k
    print("== Hanner polytopes")
    for d, (num, vs) in hanner_counts(6).items():
        print(f"d={d}: {num} explicit Hanner polytopes, vertex numbers {vs}; "
              f"range [{2*d}, {2**d}], 2^(d+1) = {2**(d+1)} attained: {2**(d+1) in vs}")
        assert min(vs) == 2 * d and max(vs) == 2 ** d and 2 ** (d + 1) not in vs
    print("ALL CHECKS PASSED")


if __name__ == "__main__":
    main()
