#!/usr/bin/env python3
"""Independent recomputation for the disproof of TLMC conjecture 00000000119.

Conjecture: there are infinitely many primes p for which the Pisano period
pi(p) (period of the Fibonacci sequence mod p) is prime.

Disproof: for every prime p >= 3 the period pi(p) is even and > 2 (det of the
Fibonacci matrix Q = [[1,1],[1,0]] is -1, so Q^n = I mod p forces (-1)^n = 1,
and pi(p) = 2 is impossible since F(2) = 1).  The only prime with prime
Pisano period is p = 2, where pi(2) = 3.

Run:  python3 reproduce.py
"""
import sys

def fib_pair(n, m):
    """(F(n) mod m, F(n+1) mod m) by fast doubling."""
    if n == 0:
        return (0 % m, 1 % m)
    a, b = fib_pair(n >> 1, m)
    c = (a * ((2 * b - a) % m)) % m
    d = (a * a + b * b) % m
    if n & 1:
        return (d, (c + d) % m)
    return (c, d)

def is_prime(k):
    if k < 2:
        return False
    i = 2
    while i * i <= k:
        if k % i == 0:
            return False
        i += 1
    return True

def pisano(p, bound=10**7):
    """Least n >= 1 with F(n) = 0 and F(n+1) = 1 (mod p), or None."""
    a, b = 0, 1
    n = 0
    while n < bound:
        a, b = b, (a + b) % p
        n += 1
        if a == 0 and b == 1:
            return n
    return None

def main():
    # 1.  The referee's data points.
    table = [(2, 3), (3, 8), (5, 20), (7, 16), (11, 10), (13, 28)]
    for p, expected in table:
        got = pisano(p)
        assert got == expected, (p, got, expected)
        print(f"pi({p}) = {got}   (prime: {is_prime(got)})")

    # 2.  Survey: the only prime whose Pisano period is prime is 2.
    specials = []
    for p in range(2, 2000):
        if is_prime(p):
            pi = pisano(p)
            if is_prime(pi):
                specials.append((p, pi))
    print("primes p < 2000 with prime pi(p):", specials)
    assert specials == [(2, 3)], specials

    # 3.  All other prime periods are even:  every prime p >= 3 has even
    #     pi(p) (the referee's claim, spot-checked up to 2000).
    for p in range(3, 2000):
        if is_prime(p):
            pi = pisano(p)
            assert pi % 2 == 0, (p, pi)
    print("all primes 3 <= p < 2000 have even pi(p)  ✓")

    print("disproof CONFIRMED: {p prime : pi(p) prime} = {(2,3)} — finite.")
    return 0

if __name__ == "__main__":
    sys.exit(main())
