#!/usr/bin/env python3
"""Independent check for the disproof of conjecture 00000007130 (Python 3 standard library only).

Method (different from the Lean proof):
  * lattice points of tP are found by exact barycentric coordinates (Cramer's rule with
    Fractions) over a generous box, directly from the VERTICES of P;
  * the facet description (primitive normals, right-hand sides) is derived from the vertices;
  * periods are found by exact Lagrange interpolation of each residue class with polynomials of
    degree <= 2 (Ehrhart: the constituents of a 2-dimensional rational polygon have degree <= 2),
    checked on all t <= TMAX.
"""
from fractions import Fraction as F
from math import gcd

TMAX = 60


def lcm(a, b):
    return a * b // gcd(a, b)


def lattice_count(V, t):
    """#(t*conv(V) ∩ Z^2) for a triangle V (list of 3 Fraction pairs), by barycentric coordinates."""
    if t == 0:
        return 1                                    # 0*P = {(0,0)}
    (x0, y0), (x1, y1), (x2, y2) = V
    det = (x1 - x0) * (y2 - y0) - (x2 - x0) * (y1 - y0)
    assert det != 0
    xs = [t * x0, t * x1, t * x2]
    ys = [t * y0, t * y1, t * y2]
    lo_x, hi_x = int(min(xs)) - 2, int(max(xs)) + 2
    lo_y, hi_y = int(min(ys)) - 2, int(max(ys)) + 2
    n = 0
    for X in range(lo_x, hi_x + 1):
        for Y in range(lo_y, hi_y + 1):
            x, y = F(X, t), F(Y, t)                 # (X, Y) in tP  <=>  (X/t, Y/t) in P
            l1 = ((x - x0) * (y2 - y0) - (x2 - x0) * (y - y0)) / det
            l2 = ((x1 - x0) * (y - y0) - (x - x0) * (y1 - y0)) / det
            l0 = 1 - l1 - l2
            if l0 >= 0 and l1 >= 0 and l2 >= 0:
                n += 1
    return n


def facets(V):
    """Primitive integer normal a and rational rhs b with a.x <= b for each edge of the triangle."""
    out = []
    for i in range(3):
        p, q, r = V[i], V[(i + 1) % 3], V[(i + 2) % 3]
        a1, a2 = q[1] - p[1], p[0] - q[0]          # normal to edge pq
        den = lcm(F(a1).denominator, F(a2).denominator)
        a1, a2 = int(a1 * den), int(a2 * den)
        g = gcd(abs(a1), abs(a2))
        a1, a2 = a1 // g, a2 // g
        b = a1 * p[0] + a2 * p[1]
        if a1 * r[0] + a2 * r[1] > b:               # orient so the third vertex satisfies it
            a1, a2, b = -a1, -a2, -b
        out.append((a1, a2, F(b)))
    return out


def interpolate(points):
    """Coefficients (constant first) of the polynomial of degree < len(points) through points."""
    k = len(points)
    coeffs = [F(0)] * k
    for i, (xi, yi) in enumerate(points):
        basis = [F(1)]
        denom = F(1)
        for j, (xj, _) in enumerate(points):
            if j == i:
                continue
            basis = [F(0)] + basis                  # multiply by (x - xj)
            for m in range(len(basis) - 1):
                basis[m] -= xj * basis[m + 1]
            denom *= (xi - xj)
        for m in range(k):
            coeffs[m] += yi * basis[m] / denom
    return coeffs


def peval(c, x):
    return sum(ci * x ** i for i, ci in enumerate(c))


def has_period(vals, p, deg=2):
    """Is t -> vals[t] (t <= TMAX) given by polynomials of degree <= deg on each class mod p?"""
    consts = []
    for r in range(p):
        ts = [t for t in range(len(vals)) if t % p == r]
        c = interpolate([(F(t), F(vals[t])) for t in ts[:deg + 1]])
        if any(peval(c, F(t)) != vals[t] for t in ts):
            return None
        consts.append(c)
    return consts


def min_period(vals, pmax=8):
    for p in range(1, pmax + 1):
        c = has_period(vals, p)
        if c is not None:
            return p, c
    return None, None


def fmt(c):
    return "[" + ", ".join(str(x) for x in c) + "]"


def analyse(name, V):
    vden = 1
    for (x, y) in V:
        vden = lcm(vden, lcm(x.denominator, y.denominator))
    fs = facets(V)
    fden = 1
    for (_, _, b) in fs:
        fden = lcm(fden, b.denominator)
    vals = [lattice_count(V, t) for t in range(TMAX + 1)]
    p, consts = min_period(vals)
    print(f"{name}: vertices {[(str(x), str(y)) for (x, y) in V]}")
    print(f"  facets a1*x + a2*y <= b: {[(a1, a2, str(b)) for (a1, a2, b) in fs]}")
    print(f"  L(0..10) = {vals[:11]}")
    print(f"  vertex-denominator lcm = {vden}, facet-rhs-denominator lcm = {fden}, "
          f"minimal period (t <= {TMAX}) = {p}")
    for r, c in enumerate(consts):
        print(f"    constituent t = {r} mod {p}: coefficients {fmt(c)}")
    return vals, vden, fden, p, consts


ok = True

# --- the counterexample T = conv{(0,0),(1,1/2),(2,0)} ---------------------------------------
T = [(F(0), F(0)), (F(1), F(1, 2)), (F(2), F(0))]
vals, vden, fden, p, consts = analyse("T", T)
formula = all(vals[t] == (t + 1) * (t + 2) // 2 for t in range(TMAX + 1))
print(f"  L_T(t) == (t+1)(t+2)/2 for all t <= {TMAX}: {formula}")
ok &= formula and vden == 2 and fden == 1 and p == 1
# the Lean-style row count: row y has 2t+1-4y points
rows = all(vals[t] == sum(max(0, 2 * t + 1 - 4 * y) for y in range(t + 1)) for t in range(TMAX + 1))
print(f"  row formula sum_y max(0, 2t+1-4y) agrees: {rows}")
ok &= rows
# coefficient denominators of the Ehrhart polynomial (t^2 + 3t + 2)/2
cden = 1
for c in consts[0]:
    cden = lcm(cden, c.denominator)
print(f"  lcm of the denominators of the Ehrhart coefficients {fmt(consts[0])} = {cden}")
ok &= cden == 2
print(f"  => vertex reading: period {p} != {vden} (clause FAILS); "
      f"coefficient-denominator reading: {p} != {cden} (FAILS)")

# --- integer-programming data of T: basis subdeterminants ---------------------------------
A = [(a1, a2) for (a1, a2, _) in facets(T)]
dets = [abs(A[i][0] * A[j][1] - A[i][1] * A[j][0]) for i in range(3) for j in range(i + 1, 3)]
dl = 1
for d in dets:
    dl = lcm(dl, d)
print(f"  basis subdeterminants |det| of facet-normal pairs: {sorted(dets)}, lcm = {dl}; "
      f"vertex lcm {vden}; period {p}")
ok &= sorted(dets) == [1, 1, 4] and dl == 4 and p == 1

# --- lattice simplex conv{(0,0),(1,0),(0,1)}: coefficient-denominator reading fails ---------
S = [(F(0), F(0)), (F(1), F(0)), (F(0), F(1))]
valsS, vdenS, fdenS, pS, constsS = analyse("standard simplex", S)
cdenS = 1
for c in constsS[0]:
    cdenS = lcm(cdenS, c.denominator)
print(f"  lattice polytope: period {pS}, vertex lcm {vdenS}, facet lcm {fdenS}, "
      f"coefficient lcm {cdenS} => coefficient reading FAILS even for lattice polytopes")
ok &= pS == 1 and vdenS == 1 and fdenS == 1 and cdenS == 2

# --- the control T2 = conv{(0,0),(1,0),(0,1/2)} ---------------------------------------------
T2 = [(F(0), F(0)), (F(1), F(0)), (F(0), F(1, 2))]
vals2, vden2, fden2, p2, consts2 = analyse("T2", T2)
f2 = all(4 * vals2[t] + t % 2 == (t + 2) ** 2 for t in range(TMAX + 1))
print(f"  4 L_T2(t) + (t mod 2) == (t+2)^2 for all t <= {TMAX}: {f2}")
ok &= f2 and vden2 == 2 and fden2 == 1 and p2 == 2
# the Lean argument against period 1, for D = 1..50: (2D+1) does not divide D*(L(2D+1) - L(0))
L2 = lambda t: ((t + 2) ** 2 - t % 2) // 4
div_ok = all((D * (L2(2 * D + 1) - L2(0))) % (2 * D + 1) != 0 for D in range(1, 51))
print(f"  (2D+1) never divides D*(L(2D+1)-L(0)) for D = 1..50: {div_ok}")
ok &= div_ok
print(f"  => facet reading: period {p2} != {fden2} (clause FAILS); vertex reading holds here ({p2} = {vden2})")

# --- McAllister-Woods family conv{(0,0),(1,(D-1)/D),(D,0)}: period 1, denominator D --------
print("McAllister-Woods triangles conv{(0,0),(1,(D-1)/D),(D,0)} (t <= 30):")
TM = TMAX
TMAX = 30
for D in range(2, 7):
    V = [(F(0), F(0)), (F(1), F(D - 1, D)), (F(D), F(0))]
    v = [lattice_count(V, t) for t in range(TMAX + 1)]
    pp, cc = min_period(v)
    print(f"  D = {D}: vertex-denominator lcm {D}, minimal period {pp}, polynomial {fmt(cc[0])}")
    ok &= pp == 1
TMAX = TM

print("ALL CHECKS PASSED" if ok else "SOME CHECK FAILED")
raise SystemExit(0 if ok else 1)
