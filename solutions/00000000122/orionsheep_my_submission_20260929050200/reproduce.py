#!/usr/bin/env python3
"""Standalone reproduction of the disproof of TLMC conjecture 00000000122.

Conjecture: for every n >= 2 there exist infinitely many primes q such that
the n-th q-Catalan number C_n(q) is prime.

Attack (n = 2):
  * standard (Gaussian-binomial) reading: C_2(q) = q^2 + 1,
  * Carlitz reading:                      C_2(q) = q + 1.
In both readings an odd prime q makes C_2(q) an even number > 2, hence
composite; the only surviving prime is q = 2 (C_2(2) = 5 resp. 3).
Consequently the n = 2 instance has exactly one prime witness, so the
conjecture is FALSE.

No third-party dependencies: primality by trial division, polynomials as
integer coefficient lists (low degree first), all divisions exact.
"""

LIMIT = 500  # enumerate primes below this bound


def isprime(n):
    if n < 2:
        return False
    i = 2
    while i * i <= n:
        if n % i == 0:
            return False
        i += 1
    return True


# ---------- exact polynomial arithmetic (coefficients low degree first) ----

def poly_mul(a, b):
    r = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            r[i + j] += x * y
    return r


def poly_add(a, b):
    n = max(len(a), len(b))
    r = [0] * n
    for i, x in enumerate(a):
        r[i] += x
    for i, x in enumerate(b):
        r[i] += x
    return r


def poly_div_exact(a, b):
    """Exact division a / b; raises if not exact."""
    a = a[:]
    assert len(a) >= len(b), "division by higher-degree polynomial"
    q = [0] * (len(a) - len(b) + 1)
    for i in reversed(range(len(q))):
        c = a[i + len(b) - 1] // b[-1]
        if c:
            q[i] = c
            for j, y in enumerate(b):
                a[i + j] -= c * y
    assert all(x == 0 for x in a), "division was not exact"
    return q


def qnum(k):
    """[k]_q = 1 + q + ... + q^(k-1)."""
    return [1] * k


def qbinom(n, k):
    """Gaussian binomial [n choose k]_q via the product formula."""
    r = [1]
    for i in range(1, k + 1):
        r = poly_div_exact(poly_mul(r, qnum(n - k + i)), qnum(i))
    return r


# ---------- 1) standard reading: C_2(q) = [4 choose 2]_q / [3]_q -----------

def check_standard():
    c2 = poly_div_exact(qbinom(4, 2), qnum(3))
    print("standard reading: C_2(q) coefficients (low degree first):", c2)
    assert c2 == [1, 0, 1], "C_2(q) should equal q^2 + 1"
    witnesses = [q for q in primes if isprime(q * q + 1)]
    print("standard reading: primes q < %d with C_2(q) = q^2+1 prime:" % LIMIT,
          witnesses)
    assert witnesses == [2], "only q = 2 should give a prime value"
    print("  boundary: C_2(2) = 5 is prime:", isprime(5))


# ---------- 2) Carlitz reading: C_0 = 1, C_{n+1} = sum_k q^k C_k C_{n-k} ---

def check_carlitz():
    cs = [[1]]
    for n in range(3):
        acc = [0]
        for k in range(n + 1):
            qk = [0] * k + [1]  # q^k
            acc = poly_add(acc, poly_mul(poly_mul(qk, cs[k]), cs[n - k]))
        cs.append(acc)
    for i, c in enumerate(cs):
        print("Carlitz reading: C_%d(q) coefficients:" % i, c)
    assert cs[1] == [1], "C_1(q) should equal 1"
    assert cs[2] == [1, 1], "C_2(q) should equal 1 + q"
    assert cs[3] == [1, 2, 1, 1], "C_3(q) should equal 1 + 2q + q^2 + q^3"
    witnesses = [q for q in primes if isprime(q + 1)]
    print("Carlitz reading: primes q < %d with C_2(q) = q+1 prime:" % LIMIT,
          witnesses)
    assert witnesses == [2], "only q = 2 should give a prime value"
    print("  boundary: Carlitz C_2(2) = 3 is prime:", isprime(3))


primes = [q for q in range(2, LIMIT) if isprime(q)]

if __name__ == "__main__":
    check_standard()
    check_carlitz()
    print()
    print("CONCLUSION: for n = 2 exactly one prime q (= 2) yields a prime")
    print("C_2(q) under both standard readings, so conjecture 00000000122")
    print("(infinitely many prime q for every n >= 2) is FALSE.")
    print("ALL CHECKS PASSED")
