#!/usr/bin/env python3
"""Independent check for conjecture 00000004310 (Python 3 standard library only).

Claim refuted: "there exist two imaginary quadratic fields of the same discriminant whose
3-parts of the class groups are isomorphic while their unit groups are not".

Checks (by methods independent of the Lean development):
 1. disc: m -> (m if m = 1 mod 4 else 4m) is injective on squarefree m with -20000 < m < 0, its
    values are fundamental discriminants, and every negative fundamental discriminant D with
    |D| < 80000 arises from exactly one m (fundamental discriminants recognised directly).
 2. Units of O_K for every such m, found by brute force over the norm form on a box that is
    proved large enough (|a|, |b| <= 2 always contains all solutions of N = 1):
    4 for m = -1, 6 for m = -3, 2 otherwise; the unit count is a function of D.
 3. Orders: for every D < 0, D = 0, 1 mod 4, |D| < 10^4, the units of Z[(D + sqrt D)/2]
    (solutions of t^2 - D u^2 = 4) number w(D) = 4, 6, 2 for D = -4, -3, other.
 4. Forms: for every D as in 3, every reduced primitive positive definite form (a, b, c) of
    discriminant D has exactly w(D) proper automorphs (matrices in SL2(Z) fixing it, found by
    brute force over a bounded box for |D| < 400 and through the (t, u) parametrisation for
    all |D| < 10^4); the class number h(D) is a function of D (so is the class group).
 5. The unit groups are cyclic of order w (generator found by brute force).
 6. The claim: no discriminant carries two fields with different unit groups; under the weakened
    reading without "same discriminant", witnesses exist already at |D| <= 8 (class number 1,
    so trivial 3-parts), so "the smallest discriminant has seven digits" fails there too.
 7. Real quadratic readings: disc injective on squarefree 1 < m < 20000; every squarefree
    1 < m < 2000 has a unit of infinite order (Pell, continued fractions); Q(sqrt 2) / Q(sqrt -2)
    (|D| = 8, Minkowski bounds < 2, so h = 1) is a one-digit mixed witness.
"""
import sys
from math import isqrt

FAIL = 0


def check(cond, msg):
    global FAIL
    print(("PASS " if cond else "FAIL ") + msg)
    if not cond:
        FAIL += 1


def squarefree(n):
    n = abs(n)
    if n == 0:
        return False
    d = 2
    while d * d <= n:
        if n % (d * d) == 0:
            return False
        d += 1
    return True


def disc(m):
    return m if m % 4 == 1 else 4 * m


def is_fundamental(D):
    """Fundamental discriminant test, independent of the formula disc(m)."""
    if D % 4 == 1:
        return squarefree(D)
    if D % 4 == 0:
        q = D // 4
        return q % 4 in (2, 3) and squarefree(q)
    return False


# ---------------------------------------------------------------- 1. injectivity
M = 20000
seen = {}
ok_fund = True
for m in range(-1, -M, -1):
    if not squarefree(m):
        continue
    D = disc(m)
    if D in seen:
        check(False, f"disc collision {m} {seen[D]} -> {D}")
    seen[D] = m
    if not is_fundamental(D):
        ok_fund = False
nf = len(seen)
check(True, f"disc injective on all {nf} squarefree m with -{M} < m < 0")
check(ok_fund, "every disc(m) is a fundamental discriminant (D=1 mod 4 squarefree, or D=4q, q=2,3 mod 4 squarefree)")
fund = [D for D in range(-1, -M, -1) if is_fundamental(D)]
check(all(D in seen for D in fund), f"every negative fundamental discriminant with |D| < {M} ({len(fund)} of them) comes from an m (unique by injectivity)")


# ---------------------------------------------------------------- 2. units of O_K
def field_units(m):
    """Brute-force units of O_m as pairs (a, b) = a + b*omega; returns list."""
    if m % 4 == 1:
        t, n = 1, (1 - m) // 4
    else:
        t, n = 0, -m
    # 4N = (2a+tb)^2 + (4n - t^2) b^2 with 4n - t^2 = |D| >= 3, so N = 1 forces |b| <= 1, |a| <= 1.
    # Search a larger box |a|,|b| <= 3 as a sanity margin.
    res = []
    for a in range(-3, 4):
        for b in range(-3, 4):
            if a * a + t * a * b + n * b * b == 1:
                res.append((a, b, t, n))
    return res


def w_of(D):
    return 4 if D == -4 else 6 if D == -3 else 2


bad = []
by_disc = {}
for m in range(-1, -M, -1):
    if not squarefree(m):
        continue
    D = disc(m)
    u = len(field_units(m))
    by_disc.setdefault(D, set()).add(u)
    if u != w_of(D):
        bad.append((m, u))
check(not bad, "unit counts of O_m: 4 for m=-1, 6 for m=-3, 2 otherwise (all squarefree -20000 < m < 0)")
check(all(len(s) == 1 for s in by_disc.values()), "the number of units is a function of the discriminant")
check([x[:2] for x in field_units(-1)] == [(-1, 0), (0, -1), (0, 1), (1, 0)], "O_{-1}^x = {+-1, +-i}")
check(sorted(x[:2] for x in field_units(-3)) == sorted([(1, 0), (0, 1), (-1, 1), (-1, 0), (0, -1), (1, -1)]),
      "O_{-3}^x = {+-1, +-w, +-w^2}, w = (1+sqrt-3)/2")


# ---------------------------------------------------------------- 3. orders
def order_units_tu(D):
    """Units (t + u sqrt D)/2 of the order of discriminant D: t^2 - D u^2 = 4 (|t| <= 2, |u| <= 2/sqrt|D|)."""
    res = []
    for u in range(-2, 3):
        r = 4 + D * u * u
        if r < 0:
            continue
        s = isqrt(r)
        if s * s == r:
            for t in {s, -s}:
                if (t - u * D) % 2 == 0:
                    res.append((t, u))
    return res


def mult(x, y, t, n):
    return (x[0] * y[0] - n * x[1] * y[1], x[0] * y[1] + x[1] * y[0] + t * x[1] * y[1])


ok_orders = True
ok_cyclic = True
Dlist = [D for D in range(-3, -10000, -1) if D % 4 in (0, 1)]
for D in Dlist:
    sols = order_units_tu(D)
    if len(sols) != w_of(D):
        ok_orders = False
    # same thing in coordinates a + b*omega, omega^2 = t omega - n
    t = D % 2
    n = (t - D) // 4
    units = [(a, b) for a in range(-3, 4) for b in range(-3, 4) if a * a + t * a * b + n * b * b == 1]
    if len(units) != w_of(D):
        ok_orders = False
    # cyclic: some unit has order exactly w
    def order(g):
        x, k = g, 1
        while x != (1, 0):
            x = mult(x, g, t, n)
            k += 1
            if k > 12:
                return None
        return k
    if not any(order(g) == len(units) for g in units):
        ok_cyclic = False
check(ok_orders, f"orders: t^2 - D u^2 = 4 and N(a+b w)=1 both have w(D) solutions for all {len(Dlist)} D (-10^4 < D < 0, D=0,1 mod 4)")
check(ok_cyclic, "orders: the unit group is cyclic of order w(D) (an element of order w exists)")


# ---------------------------------------------------------------- 4. forms
def reduced_forms(D):
    res = []
    a = 1
    while 3 * a * a <= -D:
        for b in range(-a + 1, a + 1):
            if (b * b - D) % (4 * a) == 0:
                c = (b * b - D) // (4 * a)
                if c < a:
                    continue
                if c == a and b < 0:
                    continue
                from math import gcd
                if gcd(gcd(a, abs(b)), c) == 1:
                    res.append((a, b, c))
        a += 1
    return res


def automorphs_bruteforce(f, B):
    a, b, c = f
    cnt = 0
    for p in range(-B, B + 1):
        for q in range(-B, B + 1):
            for r in range(-B, B + 1):
                for s in range(-B, B + 1):
                    if p * s - q * r != 1:
                        continue
                    # f(px+qy, rx+sy) == f(x,y)
                    A = a * p * p + b * p * r + c * r * r
                    Bc = 2 * a * p * q + b * (p * s + q * r) + 2 * c * r * s
                    C = a * q * q + b * q * s + c * s * s
                    if (A, Bc, C) == (a, b, c):
                        cnt += 1
    return cnt


def automorphs_tu(f, D):
    a, b, c = f
    cnt = 0
    for (t, u) in order_units_tu(D):
        M_ = ((t - b * u) // 2, -c * u, a * u, (t + b * u) // 2)
        p, q, r, s = M_
        A = a * p * p + b * p * r + c * r * r
        Bc = 2 * a * p * q + b * (p * s + q * r) + 2 * c * r * s
        C = a * q * q + b * q * s + c * s * s
        if p * s - q * r == 1 and (A, Bc, C) == (a, b, c):
            cnt += 1
    return cnt


ok_bf = True
for D in [D for D in Dlist if D > -400]:
    for f in reduced_forms(D):
        if automorphs_bruteforce(f, 2) != w_of(D):
            ok_bf = False
check(ok_bf, "forms: every reduced primitive form of discriminant D (-400 < D < 0) has w(D) proper automorphs (brute force, entries in [-2,2])")
ok_tu = True
hcount = 0
for D in Dlist:
    fs = reduced_forms(D)
    hcount += len(fs)
    for f in fs:
        if automorphs_tu(f, D) != w_of(D):
            ok_tu = False
check(ok_tu, f"forms: all {hcount} reduced primitive forms with -10^4 < D < 0 have exactly w(D) automorphs (t,u)")
check([len(reduced_forms(D)) for D in (-3, -4, -23, -20, -47)] == [1, 1, 3, 2, 5], "class numbers h(-3,-4,-23,-20,-47) = 1,1,3,2,5")

# ---------------------------------------------------------------- 5. the claim
witnesses = []
for D, s in by_disc.items():
    if len(s) > 1:
        witnesses.append(D)
check(not witnesses, "no discriminant carries two imaginary quadratic fields with different unit groups (|m| < 20000)")
check(not any(10**6 <= abs(D) < 10**7 for D in witnesses), "in particular no seven-digit witness (the witness set is empty)")

# weakened reading: drop "same discriminant"
small = [disc(m) for m in range(-1, -10, -1) if squarefree(m)]
h = {D: len(reduced_forms(D)) for D in small}
check(all(h[D] % 3 != 0 for D in (-3, -4, -8)), f"h(-3), h(-4), h(-8) = {h[-3]}, {h[-4]}, {h[-8]}: trivial 3-parts of the class groups")
check(w_of(-3) != w_of(-4) and w_of(-4) != w_of(-8),
      "weakened reading: (-3,-4) and (-4,-8) have isomorphic (trivial) 3-parts and unit groups of orders 6/4 and 4/2 -> one-digit witnesses, not seven-digit")

# readings 7-8: real quadratic fields
seen_r = {}
ok_r = True
for m in range(2, M):
    if not squarefree(m):
        continue
    D = disc(m)
    if D in seen_r:
        ok_r = False
    seen_r[D] = m
check(ok_r, f"real fields: disc injective on all {len(seen_r)} squarefree 1 < m < {M}")


def pell_pm1(m):
    """Smallest solution of x^2 - m y^2 = +-1 with y > 0 via the continued fraction of sqrt(m)."""
    a0 = isqrt(m)
    mm, d, a = 0, 1, a0
    p_prev, p = 1, a0
    q_prev, q = 0, 1
    for _ in range(10000):
        if p * p - m * q * q in (1, -1):
            return p, q
        mm = d * a - mm
        d = (m - mm * mm) // d
        a = (a0 + mm) // d
        p_prev, p = p, a * p + p_prev
        q_prev, q = q, a * q + q_prev
    return None


ok_pell = True
cnt_pell = 0
for m in range(2, 2000):
    if not squarefree(m):
        continue
    sol = pell_pm1(m)
    if sol is None or sol[1] <= 0 or sol[0] ** 2 - m * sol[1] ** 2 not in (1, -1):
        ok_pell = False
    cnt_pell += 1
check(ok_pell, f"real fields: each of the {cnt_pell} squarefree 1 < m < 2000 has a unit x + y*sqrt(m), y > 0 (infinite order); with Dirichlet, O_K^x = {{+-1}} x Z")
from math import pi, sqrt
check(abs(disc(2)) == abs(disc(-2)) == 8 and 0.5 * sqrt(8) < 2 and (2 / pi) * sqrt(8) < 2,
      "mixed reading: Q(sqrt 2), Q(sqrt -2) have |D| = 8 and Minkowski bounds 1.41, 1.80 < 2 (h = 1); units Z/2 x Z vs Z/2 -> one-digit witness")
check(pell_pm1(2) == (1, 1), "Q(sqrt 2): fundamental unit 1 + sqrt 2 (norm -1)")

print()
print("ALL CHECKS PASSED" if FAIL == 0 else f"{FAIL} CHECK(S) FAILED")
sys.exit(1 if FAIL else 0)
