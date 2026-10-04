"""Independent checks for conjecture 00000007672 (Python 3 standard library).

Gaussian binomials are computed here from the product formula
[n choose k]_q = prod_{i=1..k} (1 - q^{n-k+i}) / (1 - q^i) by exact polynomial
division (independent of the q-Pascal rule used in Lean).  Then
F_n(q) = sum_j [n-1-j choose j]_q q^{j^2}, and gcd(F_6, F_3) is computed in
Q[q] by the Euclidean algorithm and lifted to Z[q] by Gauss's lemma.
"""

from fractions import Fraction
from math import gcd


def strip(a):
    a = list(a)
    while a and a[-1] == 0:
        a.pop()
    return a


def add(a, b):
    n = max(len(a), len(b))
    return [(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0) for i in range(n)]


def mul(a, b):
    if not a or not b:
        return []
    r = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            r[i + j] += x * y
    return r


def divmod_q(a, b):
    """Division with remainder in Q[q]."""
    a = [Fraction(x) for x in strip(a)]
    b = [Fraction(x) for x in strip(b)]
    q = [Fraction(0)] * max(1, len(a) - len(b) + 1)
    while a and len(a) >= len(b):
        c = a[-1] / b[-1]
        d = len(a) - len(b)
        q[d] = c
        for i, y in enumerate(b):
            a[i + d] -= c * y
        a = strip(a)
    return strip(q), a


def one_minus_qpow(k):
    return [1] + [0] * (k - 1) + [-1]


def gauss(n, k):
    if k < 0 or k > n:
        return []
    num, den = [1], [1]
    for i in range(1, k + 1):
        num = mul(num, one_minus_qpow(n - k + i))
        den = mul(den, one_minus_qpow(i))
    quo, rem = divmod_q(num, den)
    assert not rem and all(c.denominator == 1 for c in quo)
    return [int(c) for c in quo]


def qfib(n):
    r = []
    for j in range(n):
        r = add(r, mul(gauss(n - 1 - j, j), [0] * (j * j) + [1]))
    return strip(r)


def ev(p, x):
    return sum(c * x ** i for i, c in enumerate(p))


def gcd_q(a, b):
    a, b = [Fraction(x) for x in strip(a)], [Fraction(x) for x in strip(b)]
    while b:
        _, r = divmod_q(a, b)
        a, b = b, r
    return [x / a[-1] for x in a]


def divides_z(b, a):
    quo, rem = divmod_q(a, b)
    return not rem and all(c.denominator == 1 for c in quo)


def main():
    F = {n: qfib(n) for n in range(1, 31)}
    print("F_1..F_7:", [F[n] for n in range(1, 8)])
    assert [ev(F[n], 1) for n in range(1, 16)] == \
        [1, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89, 144, 233, 377, 610]
    assert F[3] == [1, 1]
    assert F[6] == [1, 1, 1, 1, 2, 1, 1]
    assert ev(F[3], -1) == 0 and ev(F[6], -1) == 2
    quo, rem = divmod_q(F[6], F[3])
    print("F_6 = F_3 *", [str(c) for c in quo], "+", [str(c) for c in rem])
    assert rem == [2]
    g = gcd_q(F[6], F[3])
    assert g == [1]
    # content of F_3 is 1, so by Gauss's lemma gcd in Z[q] is the primitive
    # part of the Q[q]-gcd times gcd of contents, i.e. 1.
    print("gcd(F_6, F_3) in Q[q] = 1; contents are 1, so gcd in Z[q] = +-1")
    assert not divides_z(F[3], F[6])
    print("F_{gcd(6,3)} = F_3 = 1+q does not divide 1 = gcd(F_6, F_3): clause fails")

    fails = []
    for n in range(1, 31):
        for m in range(n + 1, 31):
            d = gcd(n, m)
            if not divides_z(F[d], F[m]) or not divides_z(F[d], F[n]):
                fails.append((n, m))
    print("pairs (n<m<=30) with F_gcd(n,m) not dividing both F_n and F_m:", len(fails))
    print("first few:", fails[:8])
    print("F_n(-1) for n=1..30:", [ev(F[n], -1) for n in range(1, 31)])
    # Schur's recurrence F_n = F_{n-1} + q^{n-2} F_{n-2}, and F_n(-1) != 0 for n != 3,
    # hence F_3 does not divide F_{3k} for every k >= 2 (checked here for 3k <= 30).
    for k in range(3, 31):
        assert F[k] == strip(add(F[k - 1], [0] * (k - 2) + F[k - 2])), k
    assert all(ev(F[n], -1) > 0 for n in range(1, 31) if n != 3)
    print("Schur recurrence holds for n = 3..30; F_n(-1) > 0 for all n != 3 up to 30")
    print("ALL CHECKS PASSED")


if __name__ == "__main__":
    main()
