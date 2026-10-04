#!/usr/bin/env python3
"""
Reproduction script for the disproof of conjecture `00000000462`.

Claim under test (as filed):
    "tau(circulant C_n(1,2)) satisfies a linear recurrence whose largest real
     characteristic root tends to alpha^2, where alpha = 2 + sqrt(3)."

Everything here uses only the Python 3 standard library and exact integer
arithmetic (no floating point where exactness matters).

What is checked:
  1. tau(C_n(1,2)) computed from the matrix-tree theorem (exact Kirchhoff
     determinant, integer Bareiss elimination) for 5 <= n <= 60.
  2. The exact closed form  tau(n) = n * (L(2n) + 2*(-1)^(n-1)) / 5,
     with L the Lucas sequence, matches the matrix-tree value for every n.
  3. The integrality statement 5 | (L(2n) + 2*(-1)^(n-1))  for all those n.
  4. The six-term linear recurrence
         tau(n+6) = 4*tau(n+5) - 10*tau(n+3) + 4*tau(n+1) - tau(n)
     holds for every n in range.
  5. The characteristic polynomial of that recurrence factorises as
         x^6 - 4x^5 + 10x^3 - 4x + 1 = ((x+1)(x^2-3x+1))^2,
     verified by exact integer polynomial multiplication.
  6. The conjectured value alpha^2 = (2+sqrt(3))^2 = 7 + 4*sqrt(3) is NOT a
     root of that characteristic polynomial: exact computation in
     Z[sqrt(3)] = Z[t]/(t^2-3) gives
         p(7 + 4*sqrt(3)) = 2615536 + 1510080*sqrt(3) != 0.
  7. The true exponential growth rate is phi^2 = (3+sqrt(5))/2 = 2.6180339887...,
     computed to high precision from the Lucas closed form, and it is nowhere
     near alpha^2 = 13.9282032302....

Exit code 0 and a final `PASS` line iff every check holds.
"""

import sys
from fractions import Fraction
from math import isqrt

FAILURES = []


def check(name, ok, detail=""):
    status = "ok  " if ok else "FAIL"
    print(f"  [{status}] {name}{('  -- ' + detail) if detail else ''}")
    if not ok:
        FAILURES.append(name)
    return ok


# ----------------------------------------------------------------------------
# 1. exact spanning-tree count of the circulant graph C_n(1,2)
# ----------------------------------------------------------------------------

def laplacian_circulant_12(n):
    """Laplacian matrix of the circulant graph C_n(1,2) (the square of C_n)."""
    L = [[0] * n for _ in range(n)]
    for i in range(n):
        for s in (1, 2):
            j = (i + s) % n
            if j != i:
                L[i][i] += 1
                L[j][j] += 1
                L[i][j] -= 1
                L[j][i] -= 1
    return L


def det_int(M):
    """Exact determinant of an integer matrix by fraction-free Bareiss elimination."""
    m = len(M)
    if m == 0:
        return 1
    A = [row[:] for row in M]
    sign = 1
    prev = 1
    for k in range(m - 1):
        if A[k][k] == 0:
            for i in range(k + 1, m):
                if A[i][k] != 0:
                    A[k], A[i] = A[i], A[k]
                    sign = -sign
                    break
            else:
                return 0
        for i in range(k + 1, m):
            for j in range(k + 1, m):
                A[i][j] = (A[i][j] * A[k][k] - A[i][k] * A[k][j]) // prev
        prev = A[k][k]
    return sign * A[m - 1][m - 1]


def tau_matrix_tree(n):
    """tau(C_n(1,2)): the number of spanning trees, via the matrix-tree theorem."""
    L = laplacian_circulant_12(n)
    minor = [row[:-1] for row in L[:-1]]
    return det_int(minor)


# ----------------------------------------------------------------------------
# 2. Lucas numbers
# ----------------------------------------------------------------------------

LUCAS_MAX = 400
L = [0] * (LUCAS_MAX + 1)
L[0], L[1] = 2, 1
for _i in range(2, LUCAS_MAX + 1):
    L[_i] = L[_i - 1] + L[_i - 2]


def u(n):
    """u(n) = L(2n) + 2*(-1)^(n-1).  Then tau(n) = n*u(n)/5."""
    return L[2 * n] + (2 if n % 2 == 1 else -2)


def tau_closed(n):
    return n * u(n) // 5


# ----------------------------------------------------------------------------
# 3. exact polynomial arithmetic on coefficient lists (ascending order)
# ----------------------------------------------------------------------------

def pmul(p, q):
    r = [0] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        for j, b in enumerate(q):
            r[i + j] += a * b
    return r


def peval(coeffs, x):
    """Evaluate an integer-coefficient polynomial at an integer x."""
    acc = 0
    for c in reversed(coeffs):
        acc = acc * x + c
    return acc


# ----------------------------------------------------------------------------
# 4. exact arithmetic in Z[sqrt(3)] = Z[t]/(t^2-3), represented as pairs
# ----------------------------------------------------------------------------

def z3_mul(x, y):
    a, b = x
    c, d = y
    return (a * c + 3 * b * d, a * d + b * c)


def z3_add(x, y):
    return (x[0] + y[0], x[1] + y[1])


def z3_sub(x, y):
    return (x[0] - y[0], x[1] - y[1])


def z3_scale(k, x):
    return (k * x[0], k * x[1])


def z3_pow(x, k):
    r = (1, 0)
    for _ in range(k):
        r = z3_mul(r, x)
    return r


def z3_poly_eval(coeffs, x):
    """Evaluate an integer-coefficient polynomial at a point of Z[sqrt(3)]."""
    acc = (0, 0)
    for c in reversed(coeffs):
        acc = z3_add(z3_mul(acc, x), (c, 0))
    return acc


def zsqrt_mul(x, y, d):
    """Multiplication in Z[sqrt(d)], represented as pairs."""
    a, b = x
    c, e = y
    return (a * c + d * b * e, a * e + b * c)


def zsqrt_poly_eval(coeffs, x, d):
    """Evaluate an integer-coefficient polynomial at a point of Z[sqrt(d)]."""
    acc = (0, 0)
    for c in reversed(coeffs):
        acc = (acc[0] * x[0] + d * acc[1] * x[1] + c,
               acc[0] * x[1] + acc[1] * x[0])
    return acc


# ----------------------------------------------------------------------------
# checks
# ----------------------------------------------------------------------------

def main():
    print("=" * 74)
    print("Disproof of conjecture 00000000462 -- reproduction")
    print("=" * 74)
    print()

    N_LO, N_HI = 5, 60

    print("[1/7] matrix-tree theorem vs the exact closed form")
    print("      tau(C_n(1,2)) = n*(L(2n) + 2*(-1)^(n-1))/5")
    mt = {}
    for n in range(N_LO, N_HI + 1):
        mt[n] = tau_matrix_tree(n)
    mism = [(n, mt[n], tau_closed(n)) for n in mt if mt[n] != tau_closed(n)]
    check(
        f"closed form matches the matrix-tree value for every {N_LO} <= n <= {N_HI}",
        not mism,
        "" if not mism else f"mismatches: {mism[:4]}",
    )
    print("      first values: " + ", ".join(f"tau({n})={mt[n]}" for n in range(5, 13)))
    print()

    print("[2/7] integrality:  5 divides L(2n) + 2*(-1)^(n-1)")
    bad_div = [n for n in range(1, 201) if u(n) % 5 != 0]
    check("5 | u(n) for every 1 <= n <= 200", not bad_div, str(bad_div[:6]))
    print()

    print("[3/7] the six-term linear recurrence")
    print("      tau(n+6) = 4*tau(n+5) - 10*tau(n+3) + 4*tau(n+1) - tau(n)")
    def tau_any(n):
        return tau_closed(n)
    bad_rec = []
    for n in range(N_LO, N_HI + 1 - 6):
        lhs = tau_any(n + 6)
        rhs = 4 * tau_any(n + 5) - 10 * tau_any(n + 3) + 4 * tau_any(n + 1) - tau_any(n)
        if lhs != rhs:
            bad_rec.append((n, lhs, rhs))
    check(f"recurrence holds for every {N_LO} <= n <= {N_HI - 6}", not bad_rec, str(bad_rec[:3]))
    print()

    print("[4/7] characteristic polynomial and its factorisation")
    P = [1, -4, 0, 10, 0, -4, 1]          # x^6 - 4x^5 + 10x^3 - 4x + 1, ascending
    Q = [1, -2, -2, 1]                    # x^3 - 2x^2 - 2x + 1
    F1 = pmul([1, 1], [1, -3, 1])         # (x+1)(x^2-3x+1)
    check("x^3 - 2x^2 - 2x + 1 = (x+1)(x^2-3x+1)", F1 == Q, f"got {F1}")
    check("(x^3-2x^2-2x+1)^2 = x^6 - 4x^5 + 10x^3 - 4x + 1", pmul(Q, Q) == P,
          f"got {pmul(Q, Q)}")
    check("so p(x) = ((x+1)(x^2-3x+1))^2", pmul(F1, F1) == P, f"got {pmul(F1, F1)}")
    print()

    print("[5/7] alpha^2 = (2+sqrt(3))^2 = 7 + 4*sqrt(3) is NOT a root of p")
    alpha = (2, 1)
    a2 = z3_mul(alpha, alpha)
    check("alpha^2 = 7 + 4*sqrt(3)", a2 == (7, 4), f"got {a2}")
    q_at = z3_add(z3_sub(z3_pow(a2, 2), z3_scale(3, a2)), (1, 0))
    check("alpha^4 - 3*alpha^2 + 1 = 77 + 44*sqrt(3) != 0", q_at == (77, 44),
          f"got {q_at}")
    p_at = z3_poly_eval(P, a2)
    check("p(alpha^2) = 2615536 + 1510080*sqrt(3) != 0", p_at == (2615536, 1510080),
          f"got {p_at}")
    check("in particular p(alpha^2) != 0, so alpha^2 is not a characteristic root",
          p_at != (0, 0))
    # a real root check, to be safe against the pair representation: both
    # coordinates are non-negative and not both zero, and sqrt(3) > 0.
    check("both coordinates of p(alpha^2) are non-negative and non-zero",
          p_at[0] >= 0 and p_at[1] >= 0 and p_at != (0, 0), f"got {p_at}")
    print()

    print("[6/7] the true largest characteristic root")
    # roots of x^2-3x+1 are (3 +- sqrt(5))/2; the even-index Lucas numbers
    # L(2n) satisfy that recurrence, so the dominant root is (3+sqrt(5))/2.
    # Since tau(n) = n*u(n)/5, dividing out the linear factor n gives a rapidly
    # convergent estimate of the exponential growth rate itself.
    ratio_num = tau_any(N_HI) * (N_HI - 1)
    ratio_den = tau_any(N_HI - 1) * N_HI
    approx = Fraction(ratio_num, ratio_den)
    raw_num = tau_any(N_HI)
    raw_den = tau_any(N_HI - 1)
    raw = Fraction(raw_num, raw_den)
    phi2 = Fraction(3, 2) + Fraction(isqrt(5 * 10**40), 2 * 10**20)
    print(f"      tau({N_HI})/tau({N_HI - 1})                    = {float(raw):.10f}  (slow: O(1/n))")
    print(f"      [tau({N_HI})/{N_HI}] / [tau({N_HI - 1})/{N_HI - 1}]   = {float(approx):.10f}  (fast)")
    print(f"      phi^2 = (3+sqrt(5))/2                 = {float(phi2):.10f}")
    print(f"      alpha^2 = 7 + 4*sqrt(3)               = {float(7 + 4 * Fraction(isqrt(3 * 10**40), 10**20)):.10f}")
    check("the growth ratio is far closer to phi^2 than to alpha^2",
          abs(float(approx) - float(phi2)) < abs(float(approx) - 13.928203230275509),
          f"ratio {float(approx):.6f}")
    check("phi^2 solves x^2 - 3x + 1, the characteristic polynomial of L(2n)",
          zsqrt_poly_eval([4, -6, 1], (3, 1), 5) == (0, 0),
          "exact check in Z[sqrt(5)] via y = 2*phi^2 = 3 + sqrt(5): y^2 - 6y + 4 = 0")
    print()

    print("[7/7] summary")
    alpha_sq_float = 7 + 4 * float(Fraction(isqrt(3 * 10**40), 10**20))
    check("alpha^2 is not a characteristic root of the recurrence", p_at != (0, 0))
    check("phi^2 != alpha^2", abs(float(phi2) - alpha_sq_float) > 1.0,
          f"phi^2 = {float(phi2):.6f}, alpha^2 = {alpha_sq_float:.6f}")
    print()

    if FAILURES:
        print(f"FAIL: {len(FAILURES)} check(s) failed: {FAILURES}")
        return 1
    print("PASS: every check verified; conjecture 00000000462 is FALSE.")
    print("The characteristic root of tau(C_n(1,2)) is phi^2 = (3+sqrt(5))/2 = 2.6180339887...,")
    print("not alpha^2 = 7 + 4*sqrt(3) = 13.9282032302..., and p(alpha^2) != 0.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
