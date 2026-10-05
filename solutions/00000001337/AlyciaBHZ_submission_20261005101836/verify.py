#!/usr/bin/env python3
"""Independent standard-library sanity checks; these are not the infinite proof."""
import math

LIMIT = 200_000
mu = [1] * (LIMIT + 1)
mu[0] = 0
prime = [True] * (LIMIT + 1)
prime[0] = prime[1] = False
for p in range(2, LIMIT + 1):
    if prime[p]:
        for n in range(p, LIMIT + 1, p):
            mu[n] *= -1
            if n != p:
                prime[n] = False
        for n in range(p * p, LIMIT + 1, p * p):
            mu[n] = 0


def outer(z):
    return 1 if z in (-1, 1) else 0


def trial_mu(n):
    result, p = 1, 2
    while p * p <= n:
        if n % p == 0:
            n //= p
            result = -result
            if n % p == 0:
                return 0
            while n % p == 0:
                n //= p
        p += 1
    if n > 1:
        result = -result
    return result


assert (outer(-1), outer(0), outer(1)) == (1, 0, 1)
counts = [0] * (LIMIT + 1)
for n in range(1, LIMIT + 1):
    assert mu[n] in (-1, 0, 1)
    counts[n] = counts[n - 1] + outer(mu[n])
for n in range(1, 1001):
    assert mu[n] == trial_mu(n)
    squarefree = all(n % (k * k) != 0 for k in range(2, math.isqrt(n) + 1))
    assert outer(mu[n]) == int(squarefree)
for n in range(0, 501):
    expansion = sum(mu[d] * (n // (d * d)) for d in range(1, math.isqrt(n) + 1))
    assert expansion == counts[n]

c = 6 / math.pi ** 2
endpoints = list(range(LIMIT + 1)) + [0.125, 0.999, 1.001, 10.5, 99.75, 1000.125, 199999.999]
for x in endpoints:
    error = abs(counts[math.floor(x)] - c * x)
    assert error <= 3 * math.sqrt(x) + 1e-10, (x, error)
    if x > 0:
        assert abs(counts[math.floor(x)] / x - c) <= 3 / math.sqrt(x) + 1e-10
print('Outer convention, trial factorization, and squarefree indicators checked for n <= 1000.')
print('Exact Mobius-floor count identity checked for 0 <= N <= 500.')
print(f'Count and normalized error bounds checked at {len(endpoints)} integer/real endpoints.')
print(f'6/pi^2 = {c:.12f}')
for n in [10, 100, 1000, 10000, 100000, LIMIT]:
    print(f'N={n:6d}: count={counts[n]:6d}, mean={counts[n]/n:.12f}, error={counts[n]-c*n:+.6f}')
print('ALL CHECKS PASSED (numerical sanity only; Lean proves the universal statements).')
