"""Independent checks for conjecture 00000000603 (Python 3 standard library).

Three routes to the Conway polynomial of the torus knot T(2,n):
  1. the skein recursion for closures of the 2-braids s1^n,
  2. the Alexander polynomial of T(p,q),
         Delta(t) = (t^{pq}-1)(t-1) / ((t^p-1)(t^q-1)),
     converted to Conway form via z^2 = t + 1/t - 2,
  3. the closed form [z^{2j}] = C(k+j, 2j) for n = 2k+1 (Fibonacci polynomials).
Then the peak position is compared with floor((p-1)(q-1)/4).
"""

from math import comb, gcd


def pmul(a, b):
    r = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            r[i + j] += x * y
    return r


def pdiv_exact(a, b):
    a = a[:]
    q = [0] * (len(a) - len(b) + 1)
    for i in range(len(q) - 1, -1, -1):
        q[i] = a[i + len(b) - 1] // b[-1]
        for j, y in enumerate(b):
            a[i + j] -= q[i] * y
    assert all(v == 0 for v in a), "division not exact"
    return q


def t_pow_minus_one(n):
    return [-1] + [0] * (n - 1) + [1]


def alexander(p, q):
    """Coefficients of t^0..t^{2g} of t^g * Delta_{T(p,q)}(t)."""
    num = pmul(t_pow_minus_one(p * q), t_pow_minus_one(1))
    return pdiv_exact(num, pmul(t_pow_minus_one(p), t_pow_minus_one(q)))


def conway_from_alexander(p, q):
    """Coefficients of z^0, z^1, ..., z^{2g} of the Conway polynomial."""
    c = alexander(p, q)
    d = len(c) - 1
    assert d % 2 == 0 and c == c[::-1] and sum(c) == 1
    g = d // 2
    # T[k] = t^k + t^{-k} as a polynomial in x = z^2 = t + 1/t - 2
    T = [[2], [2, 1]]
    for k in range(1, g):
        a = pmul([2, 1], T[k])
        b = T[k - 1] + [0] * (len(a) - len(T[k - 1]))
        T.append([u - v for u, v in zip(a, b)])
    in_x = [0] * (g + 1)
    in_x[0] += c[g]
    for k in range(1, g + 1):
        for i, v in enumerate(T[k]):
            in_x[i] += c[g + k] * v
    in_z = [0] * (2 * g + 1)
    for i, v in enumerate(in_x):
        in_z[2 * i] = v
    return in_z


def conway_skein(n):
    """Conway polynomial of the closure of s1^n, coefficients of z^0, z^1, ..."""
    prev, cur = [], [1]  # closures of s1^0 (2-component unlink), s1^1 (unknot)
    for _ in range(n):
        shifted = [0] + cur
        m = max(len(prev), len(shifted))
        nxt = [(prev[i] if i < len(prev) else 0) + (shifted[i] if i < len(shifted) else 0)
               for i in range(m)]
        prev, cur = cur, nxt
    return prev


def strip(l):
    l = l[:]
    while l and l[-1] == 0:
        l.pop()
    return l


def main():
    # 1-3: the three routes agree for T(2,n), n odd, 3 <= n <= 61.
    for n in range(3, 62, 2):
        k = (n - 1) // 2
        sk = strip(conway_skein(n))
        al = strip(conway_from_alexander(2, n))
        closed = [0] * (2 * k + 1)
        for j in range(k + 1):
            closed[2 * j] = comb(k + j, 2 * j)
        assert sk == al == closed, n
    print("skein recursion == Alexander route == closed form for T(2,n), n = 3..61")

    c25 = conway_skein(25)
    print("Conway T(2,25):", c25)
    assert c25 == [1, 0, 78, 0, 1001, 0, 5005, 0, 12870, 0, 19448, 0, 18564, 0,
                   11628, 0, 4845, 0, 1330, 0, 231, 0, 23, 0, 1]
    assert (2 - 1) * (25 - 1) // 4 == 6
    assert c25[6] < c25[10] and c25[12] < c25[10]  # readings 1 and 2 fail
    print("T(2,25): predicted 6; [z^6] = %d, [z^12] = %d < [z^10] = %d"
          % (c25[6], c25[12], c25[10]))

    c61 = conway_skein(61)
    f = (2 - 1) * (61 - 1) // 4
    assert f == 15
    peak = max(range(len(c61)), key=lambda i: c61[i])
    assert peak == 26 and all(c61[i] < c61[26] for i in range(len(c61)) if i != 26)
    assert c61[15] == 0
    assert c61[28] == 416714805914 and c61[26] == 421171648758
    assert c61[30] == 344867425584
    print("T(2,61): predicted 15; unique peak at z^26 = %d;" % c61[26],
          "[z^15] = %d, [z^28] = %d, [z^30] = %d" % (c61[15], c61[28], c61[30]))

    # Survey of all torus knots T(p,q), 2 <= p < q <= 30, reading 2.
    bad = []
    for p in range(2, 31):
        for q in range(p + 1, 31):
            if gcd(p, q) != 1:
                continue
            a = conway_from_alexander(p, q)[0::2]
            assert all(v > 0 for v in a)
            m = max(a)
            peaks = [i for i, v in enumerate(a) if v == m]
            f = (p - 1) * (q - 1) // 4
            if f not in peaks:
                bad.append((p, q, peaks, f))
    print("torus knots (p<q<=30) violating reading 2:", len(bad))
    print("smallest genus examples:",
          sorted(bad, key=lambda t: ((t[0] - 1) * (t[1] - 1), t))[:5])
    print("ALL CHECKS PASSED")


if __name__ == "__main__":
    main()
