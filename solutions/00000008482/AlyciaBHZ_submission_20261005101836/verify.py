#!/usr/bin/env python3
"""Finite numerical sanity checks; the infinite claims are proved in Lean."""
from math import sqrt, log, isclose


def x(m, n):
    assert m <= n
    return sqrt(n - m)


count = 0
for n in range(61):
    for m in range(n + 1):
        assert 0 <= x(m, n) <= n - m
        assert x(m, m + 1) == 1
        assert 0 <= x(m, n + 1) - x(m, n) <= 1 + 1e-12
        for k in range(8):
            assert x(m + k, n + k) == x(m, n)
        for l in range(m + 1):
            assert x(l, n) <= x(l, m) + x(m, n) + 1e-12
            count += 1
print(f"Checked {count} ordered triples, lengths 0..60; shifts 0..7.")
print("n             error=1/sqrt(n)       error/(log(n)/n)")
ratios = []
for exponent in (2, 4, 8, 12, 16, 20):
    n = 10 ** exponent
    error = x(0, n) / n
    assert isclose(error, 1 / sqrt(n), rel_tol=1e-14)
    ratio = error / (log(n) / n)
    assert isclose(ratio, sqrt(n) / log(n), rel_tol=1e-14)
    ratios.append(ratio)
    print(f"10^{exponent:<2}         {error:.12e}     {ratio:.12e}")
assert all(a < b for a, b in zip(ratios, ratios[1:]))
print("ALL SANITY CHECKS PASSED. Finite checks do not certify asymptotics.")
