#!/usr/bin/env python3
"""Independent verification for the disproof of conjecture 00000001749.

Degenerate simultaneous Thue system: G = 2F with F(x,y) = x*y*(x+y)
(degree 3).  At a = 195093360 (b = 2a) the system is equivalent to the
single Thue equation F = a, whose integer solutions are enumerated
exhaustively via the divisor structure: 66 solutions, exceeding the
conjectured bound (deg F)*(deg G) = 9.
Exit 0 iff all checks pass.
"""
import math
import sys


def main():
    a = 195093360
    # full divisor list from the factorization
    n = a
    divs = [1]
    d = 2
    fac = []
    while d * d <= n:
        if n % d == 0:
            pk = 0
            while n % d == 0:
                n //= d
                pk += 1
            fac.append((d, pk))
            divs = [dv * d**e for dv in divs for e in range(pk + 1)]
        d += 1
    if n > 1:
        fac.append((n, 1))
        divs = [dv * n for dv in divs] + divs
    divs = sorted(set(divs))
    print(f"a = {a} = " + " * ".join(f"{p}^{e}" for p, e in fac))
    print(f"|divisors| = {len(divs)}")

    # exhaustive solution enumeration: for each signed divisor x of a,
    # y solves y^2 + xy - a/x = 0 (disc must be a perfect square)
    sols = set()
    for x in divs:
        for sx in (x, -x):
            m = a // sx
            disc = sx * sx + 4 * m
            if disc < 0:
                continue
            s = math.isqrt(disc)
            if s * s == disc:
                for y in ((-sx + s) // 2, (-sx - s) // 2):
                    if sx * y * (sx + y) == a:
                        sols.add((sx, y))
    sols = sorted(sols)
    print(f"total integer solutions of x*y*(x+y) = {a}: {len(sols)}")
    assert all(x * y * (x + y) == a for x, y in sols)

    # the conjectured bound: (deg F)*(deg G) = 3*3 = 9
    assert len(sols) > 9, len(sols)
    print(f"bound (deg F)*(deg G) = 9 < {len(sols)} — VIOLATED")

    # distinctness of the 10 kernel-certified instances
    ten = [(-2448, 33), (-2448, 2415), (-2346, 36), (-2346, 2310),
           (-1518, 90), (-1518, 1428), (-1377, 112), (-1377, 1265),
           (-1260, 138), (-1260, 1122)]
    assert len(set(ten)) == 10
    for x, y in ten:
        assert (x, y) in sols
    print("the 10 kernel-certified instances are solutions — OK")

    print("ALL CHECKS PASS — 66 solutions > 9; the bound is violated")
    return 0


if __name__ == "__main__":
    sys.exit(main())
