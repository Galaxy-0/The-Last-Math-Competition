#!/usr/bin/env python3
"""Exact rational sanity checks of the universal coboundary identities.
These checks do not establish irrationality or density; Lean proves the
irrational-volume counterexamples without relying on this program.
"""
from fractions import Fraction as F


def fract(t):
    return t - t.numerator // t.denominator


def transfer(alpha, q, x):
    return sum((fract(x - (j + 1) * alpha) for j in range(q)), F(0))


def main():
    checks = 0
    for alpha in [F(1414213562, 10**9), F(-1414213562, 10**9),
                  F(1618033989, 10**9), F(7, 3), F(0)]:
        for q in range(1, 9):
            length = fract(q * alpha)
            for x in [F(0), length, -length, F(1), F(-2), F(1, 7), F(-8, 13)]:
                assert 0 <= transfer(alpha, q, x) <= q
                indicator = int(fract(x) < length)
                assert indicator - length == transfer(alpha, q, x) - transfer(alpha, q, x + alpha)
                for N in [0, 1, 2, 7, 31, 100]:
                    count = sum(int(fract(x + n * alpha) < length) for n in range(N))
                    discrepancy = count - N * length
                    assert discrepancy == transfer(alpha, q, x) - transfer(alpha, q, x + N * alpha)
                    assert abs(discrepancy) <= q
                    # The second coordinate always belongs to [0,1).
                    for beta in [F(0), F(-19, 7)]:
                        rectangle_count = sum(int(fract(x+n*alpha) < length and
                                                  0 <= fract(F(2, 9)+n*beta) < 1)
                                              for n in range(N))
                        assert rectangle_count == count
                    checks += 1
    print(f'PASS: {checks} exact rational orbit checks (including half-open endpoints,')
    print('negative rotations, N=0, all q=1,...,8, and rectangle reduction).')
    physical_checks()
    print('Finite checks are supplemental; irrationality and density are formally proved.')


def physical_checks():
    checks = 0
    for alpha, beta in [(F(7, 5), F(17, 10)), (F(0), F(2)),
                        (F(3, 2), F(0)), (F(1, 3), F(4, 7))]:
        c = 1 + alpha*alpha + beta*beta
        assert c > alpha + beta
        points = {}
        for k in range(-20, 21):
            u, v = fract(-k*alpha), fract(-k*beta)
            m = -((-k*alpha).numerator // (-k*alpha).denominator)
            n = -((-k*beta).numerator // (-k*beta).denominator)
            assert m-k*alpha == u and n-k*beta == v
            t = k + alpha*m + beta*n
            assert t == c*k + alpha*u + beta*v
            assert c*k <= t < c*(k+1)
            points[k] = (t, u)
        for q in range(1, 9):
            area = fract(-q*alpha)
            selected = [t for t, u in points.values() if u < area]
            for K in range(-6, 7):
                for N in [0, 1, 2, 5, 9]:
                    count = sum(c*K <= t < c*(K+N) for t in selected)
                    orbit = sum(fract(-(K+j)*alpha) < area for j in range(N))
                    assert count == orbit
                    assert abs(count-N*area) <= q
                    checks += 1
            endpoints = sorted(set([F(0), -6*c, -3*c+F(1, 7),
                                    5*c+F(2, 9)] +
                                   [points[k][0] for k in range(-4, 5)]))
            for x in endpoints:
                for y in endpoints:
                    if x <= y:
                        count = sum(x <= t < y for t in selected)
                        assert abs(count-area/c*(y-x)) <= q+2
                        checks += 1
            # Independently enumerate integer triples near the canonical ones.
            for k in range(-4, 5):
                expected = [points[k][0]] if points[k][1] < area else []
                m0 = -((-k*alpha).numerator // (-k*alpha).denominator)
                n0 = -((-k*beta).numerator // (-k*beta).denominator)
                actual = []
                for m in range(m0-2, m0+3):
                    for n in range(n0-2, n0+3):
                        if 0 <= m-k*alpha < area and 0 <= n-k*beta < 1:
                            actual.append(k+alpha*m+beta*n)
                assert actual == expected
                checks += 1
    print(f'PASS: {checks} exact rational physical-counting checks (negative indices,')
    print('canonical triples, physical cells, aligned blocks, and real interval endpoints).')


if __name__ == '__main__':
    main()
