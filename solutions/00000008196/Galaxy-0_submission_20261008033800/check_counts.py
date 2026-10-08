#!/usr/bin/env python3
"""Independent exact-arithmetic regression checks; Lean is the proof artifact."""
from fractions import Fraction

def prime(p):
    return p >= 2 and all(p % d for d in range(2, p))

assert prime(5) and prime(17)
for N in range(1, 1001):
    hit5 = {n for n in range(1, N + 1) if (2*n) % (5-1) == 0}
    hit17 = {n for n in range(1, N + 1) if (2*n) % (17-1) == 0}
    assert hit17 <= hit5
    assert len(hit5) == N // 2 and len(hit17) == N // 8
    if N % 8 == 0:
        assert Fraction(len(hit5), N) == Fraction(1, 2)
        assert Fraction(len(hit17), N) == Fraction(1, 8)
        joint = Fraction(len(hit5 & hit17), N)
        product = Fraction(len(hit5)*len(hit17), N*N)
        assert joint-product == Fraction(1, 16)
print('PASS: primality, nested events, exact counts for N=1..1000; all 125 multiples of 8 have discrepancy 1/16.')
