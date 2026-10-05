#!/usr/bin/env python3
"""Independent check for conjecture 00000009898 (Python 3 standard library only).

Different method from the Lean proof: the Lean file proves the closure properties of the
classes x, y, z by hand for representations of every dimension.  Here we instead brute-force
the WHOLE torsion-class lattice of the truncated category of representations of A2 = (1 -> 2)
over F_p (p = 2, 3), with dimension vector (d1, d2), d1, d2 <= 2:

  1. enumerate every representation V1 --F--> V2 (all d2 x d1 matrices over F_p);
  2. isomorphism classes by brute-force canonical forms under GL(d2) x GL(d1);
  3. "N is a quotient of M": search for a surjective morphism M -> N (all pairs of matrices
     commuting with the arrow);
  4. "M is an extension of L by N": for every surjective morphism p : M -> N, compute the
     kernel subrepresentation L = ker p (with an explicit basis) and its isomorphism class;
  5. torsion classes = all sets of isoclasses containing 0 and closed under 3 and 4
     (all 2^14 subsets are tested);
  6. the lattice (meet = intersection, join = smallest torsion class containing the union)
     is checked to be the pentagon N5, not distributive, with the triple x, y, z;
  7. the five classes are identified with x = {V2 = 0}, y = {F surjective}, z = {V1 = 0}.
  8. the path order of A2 (2-chain) is a forest order; the oriented 3-cycle is not a poset.
"""
from itertools import product
import sys

OK = True
DMAX = 2


def check(cond, msg):
    global OK
    print(("PASS " if cond else "FAIL ") + msg)
    if not cond:
        OK = False


# ------------------------------------------------------------- linear algebra over F_p
def matmul(A, B, p, n, k, m):
    """A is n x k, B is k x m (tuples of rows)."""
    return tuple(tuple(sum(A[i][t] * B[t][j] for t in range(k)) % p for j in range(m))
                 for i in range(n))


def apply(A, v, p, n):
    return tuple(sum(A[i][t] * v[t] for t in range(len(v))) % p for i in range(n))


def all_mats(p, n, m):
    for entries in product(range(p), repeat=n * m):
        yield tuple(tuple(entries[i * m:(i + 1) * m]) for i in range(n))


def vectors(p, n):
    return list(product(range(p), repeat=n))


def rank(A, p, n, m):
    """Rank of an n x m matrix: dimension of the image, by counting it."""
    img = {apply(A, v, p, n) for v in vectors(p, m)}
    r = 0
    while p ** r < len(img):
        r += 1
    return r


def gl(p, k):
    return [A for A in all_mats(p, k, k) if rank(A, p, k, k) == k]


def span_basis(vs, p, n):
    """Greedy basis of the span of vs (brute force spans)."""
    basis, span = [], {tuple([0] * n)}
    for v in vs:
        if v not in span:
            basis.append(v)
            span = {tuple((s[i] + c * v[i]) % p for i in range(n)) for s in span for c in range(p)}
    return basis


def coords(basis, w, p, n):
    for cs in product(range(p), repeat=len(basis)):
        if tuple(sum(c * b[i] for c, b in zip(cs, basis)) % p for i in range(n)) == w:
            return cs
    raise ValueError("not in span")


# ------------------------------------------------------------- representations of A2
def run(p):
    GL = {k: gl(p, k) for k in range(DMAX + 1)}
    reps = [(m, n, F) for m in range(DMAX + 1) for n in range(DMAX + 1) for F in all_mats(p, n, m)]

    def canon(m, n, F):
        return (m, n, min(matmul(matmul(A, F, p, n, n, m), B, p, n, m, m)
                          for A in GL[n] for B in GL[m]))

    classes = sorted({canon(*r) for r in reps})
    idx = {c: i for i, c in enumerate(classes)}
    N = len(classes)
    expected = sum(min(a, b) + 1 for a in range(DMAX + 1) for b in range(DMAX + 1))
    check(N == expected, f"F_{p}: {len(reps)} representations with d1,d2 <= {DMAX}, "
          f"{N} isoclasses = sum(min(d1,d2)+1) (one per rank)")

    # morphisms M -> N: (G1, G2) with G2 F_M = F_N G1
    def homs(M, Nr):
        (m1, n1, F1), (m2, n2, F2) = M, Nr
        G1s = list(all_mats(p, m2, m1))
        G2s = list(all_mats(p, n2, n1))
        for G1 in G1s:
            lhs = matmul(F2, G1, p, n2, m2, m1)
            for G2 in G2s:
                if matmul(G2, F1, p, n2, n1, m1) == lhs:
                    yield G1, G2

    quot = set()        # (i, j): class j is a quotient of class i
    ext = set()         # (l, i, j): class i is an extension of class l by class j
    for i, M in enumerate(classes):
        m, n, F = M
        for j, Nr in enumerate(classes):
            m2, n2, _ = Nr
            for G1, G2 in homs(M, Nr):
                if rank(G1, p, m2, m) != m2 or rank(G2, p, n2, n) != n2:
                    continue
                quot.add((i, j))
                # kernel subrepresentation
                k1 = span_basis([v for v in vectors(p, m) if apply(G1, v, p, m2) == (0,) * m2], p, m)
                k2 = span_basis([v for v in vectors(p, n) if apply(G2, v, p, n2) == (0,) * n2], p, n)
                cols = [coords(k2, apply(F, b, p, n), p, n) for b in k1]
                FK = tuple(tuple(cols[c][r] for c in range(len(k1))) for r in range(len(k2)))
                ext.add((idx[canon(len(k1), len(k2), FK)], i, j))
    check(len(quot) > 0 and len(ext) > 0,
          f"F_{p}: {len(quot)} quotient pairs, {len(ext)} extension triples computed")

    zero = idx[(0, 0, ())]

    def closed(T):
        if zero not in T:
            return False
        for (a, b) in quot:
            if a in T and b not in T:
                return False
        for (l, mm, nn) in ext:
            if l in T and nn in T and mm not in T:
                return False
        return True

    tors = [frozenset(i for i in range(N) if mask >> i & 1)
            for mask in range(1 << N) if closed({i for i in range(N) if mask >> i & 1})]
    check(len(tors) == 5, f"F_{p}: exactly {len(tors)} torsion classes (all 2^{N} subsets tested)")

    full = frozenset(range(N))
    xs = frozenset(i for i, (m, n, F) in enumerate(classes) if n == 0)
    ys = frozenset(i for i, (m, n, F) in enumerate(classes) if rank(F, p, n, m) == n)
    zs = frozenset(i for i, (m, n, F) in enumerate(classes) if m == 0)
    bot = frozenset([zero])
    check(set(tors) == {bot, xs, ys, zs, full},
          f"F_{p}: the torsion classes are 0, x={{V2=0}}, y={{F onto}}, z={{V1=0}}, mod A")

    def join(a, b):
        return min((t for t in tors if a | b <= t), key=len)

    def meet(a, b):
        t = a & b
        assert t in tors
        return t

    # all joins are well defined (unique minimal upper bound) and meets are intersections
    good = True
    for a in tors:
        for b in tors:
            ubs = [t for t in tors if a | b <= t]
            j = join(a, b)
            good &= all(j <= t for t in ubs)
            good &= (a & b) in tors
    check(good, f"F_{p}: tors is a lattice (meet = intersection, join = least torsion upper bound)")

    # N5 shape: 0 < x < y < top, 0 < z < top, z incomparable to x, y
    shape = (bot < xs < ys < full and bot < zs < full and not (zs <= ys) and not (ys <= zs)
             and not (xs <= zs) and not (zs <= xs))
    check(shape, f"F_{p}: Hasse diagram is the pentagon N5: 0<x<y<mod A, 0<z<mod A")
    lhs = meet(ys, join(xs, zs))
    rhs = join(meet(ys, xs), meet(ys, zs))
    check(lhs == ys and rhs == xs and lhs != rhs,
          f"F_{p}: y ^ (x v z) = y  but  (y ^ x) v (y ^ z) = x  -> NOT distributive")
    lhs2 = join(xs, meet(ys, zs))
    rhs2 = meet(join(xs, ys), join(xs, zs))
    check(lhs2 == xs and rhs2 == ys, f"F_{p}: x v (y ^ z) = x but (x v y) ^ (x v z) = y (dual law fails)")
    # exhaustive distributivity test
    bad = sum(1 for a in tors for b in tors for c in tors
              if meet(a, join(b, c)) != join(meet(a, b), meet(a, c)))
    check(bad > 0, f"F_{p}: exhaustive test: {bad} of {len(tors) ** 3} triples violate distributivity")
    # P1 witnesses y != x
    P1 = idx[canon(1, 1, ((1,),))]
    check(P1 in ys and P1 not in xs, f"F_{p}: P1 = (K -id-> K) lies in y but not in x")
    # {S2, P1}-closure is not a torsion class (P1 ->> S1)
    S1 = idx[canon(1, 0, ())]
    inj = frozenset(i for i, (m, n, F) in enumerate(classes) if rank(F, p, n, m) == m)
    check(not closed(set(inj)) and (P1, S1) in quot,
          f"F_{p}: {{F injective}} = add{{S2,P1}} is not a torsion class (P1 ->> S1)")


# ------------------------------------------------------------- path orders
def path_order(n, arrows):
    R = {(i, i) for i in range(n)} | set(arrows)
    changed = True
    while changed:
        changed = False
        for (a, b) in list(R):
            for (c, d) in list(R):
                if b == c and (a, d) not in R:
                    R.add((a, d))
                    changed = True
    return R


def is_forest(n, R):
    antisym = all(not ((i, j) in R and (j, i) in R) or i == j for i in range(n) for j in range(n))
    down = all((i, j) in R or (j, i) in R for v in range(n) for i in range(n) for j in range(n)
               if (i, v) in R and (j, v) in R)
    up = all((i, j) in R or (j, i) in R for v in range(n) for i in range(n) for j in range(n)
             if (v, i) in R and (v, j) in R)
    return antisym and down and up


def main():
    for p in (2, 3):
        run(p)
    A2 = path_order(2, [(0, 1)])
    check(A2 == {(0, 0), (1, 1), (0, 1)} and is_forest(2, A2),
          "path order of A2 is the 2-chain 0 < 1, a forest order (down- and up-sets are chains)")
    C3 = path_order(3, [(0, 1), (1, 2), (2, 0)])
    check(not is_forest(3, C3), "the oriented 3-cycle's path relation is not antisymmetric")
    print("ALL CHECKS PASSED" if OK else "SOME CHECK FAILED")
    sys.exit(0 if OK else 1)


if __name__ == "__main__":
    main()
