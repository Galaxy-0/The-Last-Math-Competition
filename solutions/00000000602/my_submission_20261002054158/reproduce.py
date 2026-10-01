#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Independent recomputation of the attack numbers used to disprove
TLMC conjecture 00000000602.

Conjecture: for every alternating knot K, with V_K the Jones polynomial
and omega a primitive fourth root of unity (omega = +-i):
  (1) |V_K(omega)|^2 divides det(K)^2, and
  (2) det(K)^2 / |V_K(omega)|^2 = |V_K(i)|^2.

Attack (omega = +-i  =>  |V_K(omega)|^2 = |V_K(i)|^2): clause (2) collapses
to det(K)^2 = |V_K(i)|^4.

Primary witness K = right-handed trefoil 3_1 (alternating):
the Jones polynomial is recomputed here from scratch via the Kauffman
bracket state-sum on the standard PD code (no external packages),
then evaluated exactly on Gaussian integers.

Secondary witnesses (published Jones polynomials, e.g. KnotInfo/KnotAtlas):
4_1, 5_1, 5_2, 7_1, all alternating, all evaluated exactly the same way.

Pure standard library; runs offline:  python3 reproduce.py
"""

from itertools import product
from collections import defaultdict

# ----------------------------------------------------------------------
# Gaussian-integer arithmetic (exact)
# ----------------------------------------------------------------------

def gmul(x, y):
    a, b = x
    c, d = y
    return (a * c - b * d, a * d + b * c)

def gpow(t, n):
    r = (1, 0)
    for _ in range(abs(n)):
        r = gmul(r, t)
    if n < 0:
        r = (r[0], -r[1])  # on the unit circle t^(-1) = conj(t)
    return r

def peval(poly, t):
    """Evaluate Laurent polynomial {exponent: int coeff} at Gaussian t."""
    return tuple(sum(c * gpow(t, e)[j] for e, c in poly.items()) for j in (0, 1))

def nsq(z):
    return z[0] * z[0] + z[1] * z[1]

I = (0, 1)    # i
NI = (0, -1)  # -i

# ----------------------------------------------------------------------
# Kauffman bracket state-sum (full independent recomputation for 3_1)
# ----------------------------------------------------------------------

def kauffman_bracket(pd):
    """Bracket polynomial as {A-exponent: coeff} from a PD code
    [(a,b,c,d), ...] with a=in-under, b=out-under, c=out-over, d=in-over."""
    n = len(pd)
    occ = []
    for ci, (a, b, c, d) in enumerate(pd):
        occ += [(ci, a), (ci, b), (ci, c), (ci, d)]

    parent = list(range(len(occ)))

    def find(p, x):
        while p[x] != x:
            p[x] = p[p[x]]
            x = p[x]
        return x

    def union(p, x, y):
        rx, ry = find(p, x), find(p, y)
        if rx != ry:
            p[rx] = ry

    # each diagram edge joins its two occurrences
    for e in range(1, 2 * n + 1):
        idxs = [i for i, (ci, ed) in enumerate(occ) if ed == e]
        assert len(idxs) == 2, "bad PD code: edge %d occurs %d times" % (e, len(idxs))
        union(parent, idxs[0], idxs[1])
    base = parent[:]

    def loops(state):
        p = base[:]
        for ci, (a, b, c, d) in enumerate(pd):
            ia = occ.index((ci, a)); ib = occ.index((ci, b))
            ic = occ.index((ci, c)); idd = occ.index((ci, d))
            if state[ci] == 0:      # A-smoothing joins (a,d) and (b,c)
                union(p, ia, idd); union(p, ib, ic)
            else:                   # B-smoothing joins (a,b) and (c,d)
                union(p, ia, ib); union(p, ic, idd)
        return len({find(p, i) for i in range(len(occ))})

    def dpow(poly, k):  # multiply Laurent dict by (-A^2 - A^-2)^k
        cur = dict(poly)
        for _ in range(k):
            nxt = defaultdict(int)
            for e, c in cur.items():
                nxt[e + 2] += -c
                nxt[e - 2] += -c
            cur = dict(nxt)
        return cur

    full = defaultdict(int)
    for st in product([0, 1], repeat=n):
        na, nb = st.count(0), st.count(1)
        L = loops(st)
        for e, c in dpow({na - nb: 1}, L - 1).items():
            full[e] += c
    return {e: c for e, c in sorted(full.items()) if c}

def jones_from_bracket(bracket, w):
    """V(t) = (-A)^(-3w) <K> with A = t^(-1/4):
       V(t) = (-1)^w * sum_k c_k t^((3w-k)/4)."""
    P = defaultdict(int)
    for k, c in bracket.items():
        assert (3 * w - k) % 4 == 0, "non-Laurent result (wrong writhe sign?)"
        P[(3 * w - k) // 4] += (-1) ** w * c
    return {e: c for e, c in sorted(P.items()) if c}

# ----------------------------------------------------------------------
# Primary witness: 3_1 from scratch
# ----------------------------------------------------------------------

def check_conjecture(name, V, det):
    vi, vni = peval(V, I), peval(V, NI)
    # real coefficients => V(-i) = conj(V(i)), so |V(-i)|^2 = |V(i)|^2:
    # the conjectured quantity |V(omega)|^2 is the same for omega = +-i.
    assert nsq(vi) == nsq(vni), "V(i) and V(-i) have different |.|^2??"
    m = nsq(vi)                     # |V(i)|^2 = |V(omega)|^2 (omega = +-i)
    d2 = det * det
    divides = (m != 0) and (d2 % m == 0)
    quotient = d2 // m if divides else None
    clause2 = (divides and quotient == m)
    print(f"  {name}")
    print(f"    V(i) = {vi},  V(-i) = {vni}  -> |V(omega)|^2 = |V(i)|^2 = {m} (same for omega = +-i)")
    print(f"    det = {det} -> det^2 = {d2}")
    print(f"    clause (1): {m} | {d2} ? {divides}")
    print(f"    clause (2): quotient {d2}/{m} = {quotient}  ==  {m} ? {clause2}")
    verdict = divides and clause2
    print(f"    conjecture holds for {name}: {verdict}")
    return verdict

def main():
    print("=== primary witness: right-handed trefoil 3_1 (full state-sum) ===")
    pd31 = [(1, 4, 2, 5), (3, 6, 4, 1), (5, 2, 6, 3)]  # KnotAtlas PD, writhe +3
    bracket = kauffman_bracket(pd31)
    print(f"  Kauffman bracket <3_1> = {bracket}")
    assert bracket == {-7: 1, -3: -1, 5: -1}, "unexpected bracket"
    V31 = jones_from_bracket(bracket, 3)
    print(f"  Jones V(t) = {V31}")
    assert V31 == {1: 1, 3: 1, 4: -1}, "expected V(t) = t + t^3 - t^4"
    assert sum(V31.values()) == 1, "normalization V(1) = 1 failed"

    fails = []
    if not check_conjecture("3_1 (recomputed from scratch)", V31, 3):
        fails.append("3_1")

    print("\n=== secondary witnesses (published Jones polynomials, exact eval) ===")
    published = [
        ("4_1: V = t^-2 - t^-1 + 1 - t + t^2",
         {-2: 1, -1: -1, 0: 1, 1: -1, 2: 1}, 5),
        ("5_1: V = t^2 + t^4 - t^5 + t^6 - t^7",
         {2: 1, 4: 1, 5: -1, 6: 1, 7: -1}, 5),
        ("5_2: V = t + t^3 - t^4 + t^5 - t^6",
         {1: 1, 3: 1, 4: -1, 5: 1, 6: -1}, 7),
        ("7_1: V = t^3 + t^5 - t^6 + t^7 - t^8 + t^9 - t^10",
         {3: 1, 5: 1, 6: -1, 7: 1, 8: -1, 9: 1, 10: -1}, 7),
    ]
    for name, V, det in published:
        if not check_conjecture(name, V, det):
            fails.append(name.split(":")[0])

    print("\n=== verdict ===")
    print(f"  alternating counterexamples found: {fails}")
    print("  conjecture 00000000602 is FALSE"
          if fails else "  no counterexample found?!")
    # decisive numbers for the primary witness (mirrored by Lean's Main.lean):
    #   |V(omega)|^2 = |V(i)|^2 = 1, det(3_1)^2 = 9, quotient 9/1 = 9 != 1.
    assert nsq(peval(V31, I)) == 1 and 3 * 3 != nsq(peval(V31, I))
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
