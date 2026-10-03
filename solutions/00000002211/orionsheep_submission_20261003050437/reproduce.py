#!/usr/bin/env python3
"""Independent verification for the disproof of conjecture 00000002211.

d = 6 and d = 14 share the smallest prime factor 2, but the class
numbers of their rings of integers differ: h(-24) = 2 (so Z[sqrt(-6)]
is half-factorial, rho = 1, by Carlitz) and h(-56) = 4 (so
rho(Z[sqrt(-14)]) > 1). Hence rho is not a function of spf(d).
Exit 0 iff all checks pass.
"""
import sys
from math import gcd


def reduced_forms(D):
    """Reduced primitive positive-definite binary quadratic forms of
    discriminant D < 0: |b| <= a <= c, b >= 0 when |b| = a or a = c,
    b^2 = D (mod 4a), c = (b^2 - D) / (4a), gcd(a,b,c) = 1."""
    out = []
    a = 1
    while 3 * a * a <= abs(D):
        for b in range(-a, a + 1):
            if (b * b - D) % (4 * a) == 0:
                c = (b * b - D) // (4 * a)
                if a <= c and ((abs(b) < a and a < c) or b >= 0):
                    if gcd(gcd(a, b), c) == 1:
                        out.append((a, b, c))
        a += 1
    return sorted(set(out))


def main():
    # 1. class numbers via reduced forms
    f24 = reduced_forms(-24)
    f56 = reduced_forms(-56)
    print(f"disc -24: h = {len(f24)}: {f24}")
    print(f"disc -56: h = {len(f56)}: {f56}")
    assert len(f24) == 2, "h(-24) must be 2"
    assert len(f56) == 4, "h(-56) must be 4"
    assert set(f24) == {(1, 0, 6), (2, 0, 3)}
    assert set(f56) == {(1, 0, 14), (2, 0, 7), (3, -2, 5), (3, 2, 5)}

    # 2. shared smallest prime factor: both d are even, 2 is minimal prime
    assert 6 % 2 == 0 and 14 % 2 == 0
    assert all(p % 2 == 1 for p in range(3, 2))  # no prime below 2
    print("spf(6) = spf(14) = 2 — OK")

    # 3. the size bound used by the Lean enumeration
    assert 3 * 2 * 2 <= 24 < 3 * 3 * 3      # a <= 2 for D = -24
    assert 3 * 4 * 4 <= 56 < 3 * 5 * 5      # a <= 4 for D = -56
    print("size bound 3a^2 <= |D|: a <= 2 (resp. a <= 4) — OK")

    # 4. Carlitz comparison: h = 2 -> rho = 1; h = 4 > 2 -> rho > 1
    assert len(f24) <= 2 < len(f56)
    print("h(-24) = 2 <= 2 < 4 = h(-56): rho differs, spf does not — OK")

    print("ALL CHECKS PASS — rho(Z[-6]) = 1 < rho(Z[-14]), same spf = 2")
    return 0


if __name__ == "__main__":
    sys.exit(main())
