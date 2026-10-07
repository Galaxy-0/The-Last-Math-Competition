#!/usr/bin/env python3
"""Exact finite sanity checks; these checks are not the universal proof."""
from fractions import Fraction
from math import isqrt

ALLOWED = {4, 5, 6, 10}


def hyperbolic(p, q):
    return p >= 3 and q >= 3 and Fraction(1, p) + Fraction(1, q) < Fraction(1, 2)


def check_discriminant(n):
    d = n * n - 4
    assert (n - 1) ** 2 < d < n * n
    assert isqrt(d) ** 2 != d


def main():
    assert hyperbolic(4, 6)
    s = (4 - 2) * (6 - 2)
    assert s == 8 and s not in ALLOWED
    assert s - 2 == 6
    assert 6 * 6 - 4 == 32
    # Exact arithmetic in Q(sqrt(2)), with a+b*sqrt(2) stored as (a,b).
    for b in (2, -2):
        a = 3
        constant = a * a + 2 * b * b - 6 * a + 1
        sqrt_coefficient = 2 * a * b - 6 * b
        assert constant == 0 and sqrt_coefficient == 0
        assert a * a - 2 * b * b == 1  # conjugate = inverse
    print('PASS: {4,6}, S=8, N=6, and both exact roots 3 +/- 2*sqrt(2).')
    for n in range(3, 10001):
        check_discriminant(n)
    print('PASS: discriminants for every integer 3 <= N <= 10000.')
    count = outside = 0
    for p in range(3, 101):
        for q in range(3, 101):
            if hyperbolic(p, q):
                s = (p - 2) * (q - 2)
                assert s >= 5
                check_discriminant(s - 2)
                count += 1
                outside += s not in ALLOWED
    print(f'PASS: {count} hyperbolic pairs with 3 <= p,q <= 100; '
          f'{outside} have S outside the claimed list.')
    for k in range(1001):
        t = max(k, 6)
        assert t >= k and hyperbolic(t, t)
        s = (t - 2) ** 2
        assert s >= 16 and s not in ALLOWED
        check_discriminant(s - 2)
    print('PASS: diagonal witnesses t=max(K,6) for 0 <= K <= 1000.')
    print('ALL CHECKS PASSED (finite sanity checks only).')


if __name__ == '__main__':
    main()
