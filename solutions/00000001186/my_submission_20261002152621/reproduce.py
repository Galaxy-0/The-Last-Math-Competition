#!/usr/bin/env python3
"""Independent verification for the disproof of conjecture 00000001186."""
import sys

def factorize(n):
    f, d = {}, 2
    while d * d <= n:
        while n % d == 0:
            f[d] = f.get(d, 0) + 1
            n //= d
        d += 1
    if n > 1:
        f[n] = f.get(n, 0) + 1
    return f

def check():
    f = factorize(504)
    assert f == {2: 3, 3: 2, 7: 1}, f
    print(f"504 = {' * '.join(f'{p}^{e}' for p, e in sorted(f.items()))}")
    print(f"distinct prime factors of 504: {len(f)} (conjecture's m(4) needs exactly 4)")
    assert len(f) == 3
    # exhaustive divisor scan: every prime divisor is in {2,3,7}
    primes = [p for p in range(2, 505) if all(p % d for d in range(2, p)) and p > 1 and 504 % p == 0]
    assert primes == [2, 3, 7], primes
    print(f"prime divisors of 504 (exhaustive scan 2..504): {primes}")
    # ratio clause
    m3, m4 = 60, 504  # the conjecture's own asserted values
    assert m4 > 4 * m3, "ratio clause would hold"
    print(f"m(4)/m(3) = {m4}/{m3} = {m4/m3} > 4  (and {m4} != 4*{m3} = {4*m3})")
    assert m4 > 3 * m3
    print("even the bound m(4) <= 3*m(3) = 180 fails")
    print("ALL CHECKS PASS — conjecture 00000001186 refuted by its own numbers")
    return 0

if __name__ == "__main__":
    sys.exit(check())
