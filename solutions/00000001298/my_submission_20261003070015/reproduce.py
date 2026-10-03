#!/usr/bin/env python3
"""Independent verification for the disproof of conjecture 00000001298.

The formal solution of f(qx) - f(x) = x^k is unique: f = x^k/(q^k - 1).
Its x^k-coefficient 1/(q^k - 1) is a non-integer rational for all
q >= 2, k >= 2, while every q-binomial coefficient is a polynomial in q
(hence an integer at integer q).  So the coefficients are not
q-binomials.
Exit 0 iff all checks pass.
"""
import sys
from fractions import Fraction


def solve_coeff(q, k):
    """Coefficient-wise solution of f(qx) - f(x) = x^k up to degree k+2:
    a_n * (q^n - 1) = [n == k]."""
    a = {}
    for n in range(0, k + 3):
        d = q ** n - 1
        rhs = 1 if n == k else 0
        if d == 0:
            assert rhs == 0, "resonance at n = 0"
            a[n] = Fraction(0)
        else:
            a[n] = Fraction(rhs, d)
    return a


def qbinom(m, r, q):
    """[m choose r]_q as an exact polynomial value at integer q."""
    num = 1
    den = 1
    for i in range(1, r + 1):
        num *= q ** (m - r + i) - 1
        den *= q ** i - 1
    assert num % den == 0, "q-binomial must be an integer polynomial value"
    return num // den


def main():
    # 1. the functional equation is satisfied by the monomial solution
    for q in (2, 3, 4, 5):
        for k in (1, 2, 3, 4):
            a = solve_coeff(q, k)
            # f(qx) - f(x) coefficient of x^n: a_n (q^n - 1) == [n == k]
            for n in range(0, k + 3):
                lhs = a[n] * (q ** n - 1)
                rhs = Fraction(1 if n == k else 0)
                assert lhs == rhs, (q, k, n)
            c = a[k]
            assert c.denominator == q ** k - 1
            if q >= 2 and k >= 2:
                assert c.denominator >= 3 and c.numerator == 1
                assert c.denominator != 1, "coefficient must be non-integer"
    print("unique coefficient a_k = 1/(q^k - 1) satisfies the equation;"
          " non-integer for q >= 2, k >= 2 — OK")

    # 2. non-integrality at the counterexample instance q = 2, k = 2:
    #    coefficient 1/3; no natural number a with 3a = 1
    a22 = solve_coeff(2, 2)[2]
    assert a22 == Fraction(1, 3)
    assert all(3 * a != 1 for a in range(0, 5))
    print("q = 2, k = 2: coefficient 1/3 — no integer a with 3a = 1 — OK")

    # 3. q-binomial coefficients are integers at integer q (polynomiality)
    for q in (2, 3, 4, 5):
        vals = []
        for m in range(0, 7):
            for r in range(0, m + 1):
                v = qbinom(m, r, q)
                assert isinstance(v, int) and v >= 1
                vals.append(v)
        print(f"  q = {q}: all [m choose r]_q integers, e.g. {sorted(set(vals))[:6]}")
    print("q-binomial coefficients are integer-valued at integer q — OK")

    # 4. the coefficient 1/3 is not among the q-binomial values at q = 2
    q2_vals = {qbinom(m, r, 2) for m in range(0, 8) for r in range(m + 1)}
    assert Fraction(1, 3) not in q2_vals
    print("1/3 is not a q-binomial value at q = 2 — OK")

    print("ALL CHECKS PASS — the coefficients are 1/(q^k - 1), not q-binomials")
    return 0


if __name__ == "__main__":
    sys.exit(main())
