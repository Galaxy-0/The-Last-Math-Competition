"""Supplementary enumeration for conjecture 00000001854 (supports only the remark in main.tex).

For small n and prime q it lists every n x n matrix over F_q, computes the characteristic
polynomial det(X I - M) by the Leibniz expansion, tests squarefreeness by gcd(f, f') = 1
(valid over a perfect field), and compares the count with the proposed closed form.
"""
from fractions import Fraction
from itertools import permutations, product
import json


def trim(a):
    while a and a[-1] == 0:
        a = a[:-1]
    return a


def polymul(a, b, p):
    r = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            r[i + j] = (r[i + j] + x * y) % p
    return r


def polymod(a, b, p):
    a, b = trim(a[:]), trim(b[:])
    inv = pow(b[-1], p - 2, p)
    while len(a) >= len(b):
        c = a[-1] * inv % p
        s = len(a) - len(b)
        for i, y in enumerate(b):
            a[s + i] = (a[s + i] - c * y) % p
        a = trim(a)
    return a


def polygcd(a, b, p):
    a, b = trim(a[:]), trim(b[:])
    while b:
        a, b = b, polymod(a, b, p)
    return a


def derivative(a, p):
    return trim([(i * a[i]) % p for i in range(1, len(a))])


def charpoly(m, n, p):
    res = [0] * (n + 1)
    for perm in permutations(range(n)):
        sign = 1
        for i in range(n):
            for j in range(i + 1, n):
                if perm[i] > perm[j]:
                    sign = -sign
        term = [1]
        for i in range(n):
            j = perm[i]
            entry = [(-m[i][j]) % p, 1] if i == j else [(-m[i][j]) % p]
            term = polymul(term, entry, p)
        for k, c in enumerate(term):
            res[k] = (res[k] + sign * c) % p
    return res


def squarefree(f, p):
    d = derivative(f, p)
    return bool(d) and len(polygcd(f, d, p)) == 1


def count(n, p):
    total = 0
    for entries in product(range(p), repeat=n * n):
        m = [list(entries[i * n:(i + 1) * n]) for i in range(n)]
        if squarefree(charpoly(m, n, p), p):
            total += 1
    return total


def formula(n, q, upper):
    value = Fraction(q) ** (n * n)
    for i in range(1, upper + 1):
        value *= 1 - Fraction(1, q ** (i * i))
    return value


def main():
    rows = []
    for n, q in [(1, 2), (1, 3), (1, 5), (2, 2), (2, 3), (2, 5), (3, 2), (3, 3)]:
        c = count(n, q)
        a = formula(n, q, n)
        b = formula(n, q, n - 1)
        rows.append({"n": n, "q": q, "count": c,
                     "formula_product_1_to_n": str(a),
                     "formula_product_1_to_n_minus_1": str(b),
                     "equals_reading_A": a == c})
    expected = {(1, 2): 2, (1, 3): 3, (1, 5): 5, (2, 2): 8, (2, 3): 54, (2, 5): 500,
                (3, 2): 160, (3, 3): 11178}
    for row in rows:
        assert row["count"] == expected[(row["n"], row["q"])], row
        assert not row["equals_reading_A"], row
        if row["n"] == 1:
            assert row["count"] == row["q"]
        if row["n"] == 2:
            assert row["count"] == row["q"] ** 4 - row["q"] ** 3
    print(json.dumps({"rows": rows, "all_checks_passed": True}, indent=2))


if __name__ == "__main__":
    main()
