#!/usr/bin/env python3
"""Independent check for conjecture 00000008579 (Python 3 standard library only).

The Ornstein-Uhlenbeck generator on polynomials in d Gaussian coordinates is
    L = sum_i (d^2/dx_i^2 - x_i d/dx_i),   N = -L.
We build the matrix of L on the monomial basis of polynomials of degree <= D and compute
the kernel dimension of (L + n) exactly over the rationals (fractions.Fraction), i.e. the
multiplicity of the eigenvalue n of N.  This is a different method from the Lean proof
(which works with coefficient recursions and explicit eigenvectors).
"""
from fractions import Fraction
from itertools import combinations_with_replacement, permutations
from math import comb
import sys

FAIL = []


def check(cond, msg):
    print(("PASS " if cond else "FAIL ") + msg)
    if not cond:
        FAIL.append(msg)


# ---------- partition numbers ----------
def partitions(n, maxpart=None):
    if maxpart is None:
        maxpart = n
    if n == 0:
        yield ()
        return
    for k in range(min(n, maxpart), 0, -1):
        for rest in partitions(n - k, k):
            yield (k,) + rest


def p_euler(N):
    """p(0..N) via Euler's pentagonal number recurrence."""
    p = [1] + [0] * N
    for n in range(1, N + 1):
        s, k = 0, 1
        while True:
            g1 = k * (3 * k - 1) // 2
            g2 = k * (3 * k + 1) // 2
            if g1 > n:
                break
            sign = 1 if k % 2 else -1
            s += sign * p[n - g1]
            if g2 <= n:
                s += sign * p[n - g2]
            k += 1
        p[n] = s
    return p


P = p_euler(400)
check(all(P[n] == sum(1 for _ in partitions(n)) for n in range(0, 21)),
      "p(n) by pentagonal recurrence agrees with direct enumeration for n <= 20")
check(P[:8] == [1, 1, 2, 3, 5, 7, 11, 15], "p(0..7) = 1, 1, 2, 3, 5, 7, 11, 15")


# ---------- polynomials as dicts {exponent tuple: Fraction} ----------
def monomials(d, D):
    """All exponent tuples in d variables of total degree <= D."""
    out = []
    for deg in range(D + 1):
        for c in combinations_with_replacement(range(d), deg):
            e = [0] * d
            for i in c:
                e[i] += 1
            out.append(tuple(e))
    return out


def add(f, g, c=1):
    h = dict(f)
    for k, v in g.items():
        h[k] = h.get(k, 0) + c * v
        if h[k] == 0:
            del h[k]
    return h


def deriv(f, i):
    h = {}
    for e, c in f.items():
        if e[i] > 0:
            e2 = list(e); e2[i] -= 1
            h = add(h, {tuple(e2): c * e[i]})
    return h


def mulx(f, i):
    h = {}
    for e, c in f.items():
        e2 = list(e); e2[i] += 1
        h = add(h, {tuple(e2): c})
    return h


def L(f, d, weights=None):
    """sum_i w_i (d_i^2 f - x_i d_i f); weights=None means w_i = 1 (the OU operator)."""
    h = {}
    for i in range(d):
        w = 1 if weights is None else weights[i]
        di = deriv(f, i)
        h = add(h, deriv(di, i), w)
        h = add(h, mulx(di, i), -w)
    return h


def rank(rows):
    """Exact rank of a list of rows (lists of Fractions) by Gaussian elimination."""
    rows = [list(r) for r in rows]
    r = 0
    ncols = len(rows[0]) if rows else 0
    for c in range(ncols):
        piv = next((i for i in range(r, len(rows)) if rows[i][c] != 0), None)
        if piv is None:
            continue
        rows[r], rows[piv] = rows[piv], rows[r]
        pv = rows[r][c]
        for i in range(len(rows)):
            if i != r and rows[i][c] != 0:
                fac = rows[i][c] / pv
                rows[i] = [a - fac * b for a, b in zip(rows[i], rows[r])]
        r += 1
    return r


def eig_dim(d, n, D, weights=None, basis=None):
    """dim ker(L + n) on the span of `basis` (default: all monomials of degree <= D)."""
    if basis is None:
        basis = [{m: Fraction(1)} for m in monomials(d, D)]
    mons = monomials(d, D)
    idx = {m: k for k, m in enumerate(mons)}
    cols = []
    for b in basis:
        img = add(L(b, d, weights), b, n)
        col = [Fraction(0)] * len(mons)
        for e, c in img.items():
            col[idx[e]] = Fraction(c)
        cols.append(col)
    return len(basis) - rank(cols)


# ---------- 1. sanity: L x_i = -x_i, L(x^2-1) = -2(x^2-1), Hermite polynomials ----------
for d in (2, 3):
    for i in range(d):
        e = [0] * d; e[i] = 1
        xi = {tuple(e): Fraction(1)}
        check(L(xi, d) == {tuple(e): Fraction(-1)}, f"d={d}: L x_{i} = -x_{i}")
H2 = {(2,): Fraction(1), (0,): Fraction(-1)}
check(L(H2, 1) == {(2,): Fraction(-2), (0,): Fraction(2)}, "d=1: L(x^2 - 1) = -2 (x^2 - 1)")
H = [{(0,): Fraction(1)}, {(1,): Fraction(1)}]
for n in range(1, 12):
    H.append(add(mulx(H[n], 0), H[n - 1], -n))   # H_{n+1} = x H_n - n H_{n-1}
check(all(L(H[n], 1) == add({}, H[n], -n) for n in range(13)) and
      all(H[n].get((n,)) == 1 for n in range(13)),
      "d=1: Hermite H_n (H_{n+1} = x H_n - n H_{n-1}) is monic and satisfies L H_n = -n H_n for n <= 12")

# ---------- 2. multiplicities on R^d ----------
print()
print("multiplicity of eigenvalue n of N on polynomials in d variables (degree <= n):")
print("   d \\ n " + "".join(f"{n:>5}" for n in range(6)))
print("   p(n)  " + "".join(f"{P[n]:>5}" for n in range(6)))
table = {}
for d in range(1, 5):
    row = []
    for n in range(6):
        m = eig_dim(d, n, n)
        table[(d, n)] = m
        row.append(m)
    print(f"   d={d}   " + "".join(f"{m:>5}" for m in row))
check(all(table[(d, n)] == comb(n + d - 1, d - 1) for d in range(1, 5) for n in range(6)),
      "mult_d(n) = C(n+d-1, d-1) for d = 1..4, n = 0..5")
# the degree bound is no restriction: enlarging to degree <= n + 2 adds nothing
check(all(eig_dim(d, n, n + 2) == table[(d, n)] for d in range(1, 4) for n in range(5)),
      "same kernel dimension on degree <= n+2 (d = 1..3, n = 0..4): eigenvectors have degree n")
check(all(eig_dim(d, 0, 3) == 1 for d in range(1, 4)) and
      all(eig_dim(1, n, 6) == 1 for n in range(7)),
      "d=1: every eigenvalue n <= 6 has multiplicity exactly 1 (degree <= 6)")
for d in range(1, 5):
    bad = [n for n in range(6) if table[(d, n)] != P[n]]
    check(len(bad) > 0 and bad[0] == (2 if d == 1 else 1),
          f"d={d}: partition law fails; first failure at n={bad[0]} "
          f"(mult={table[(d, bad[0])]}, p={P[bad[0]]}); all failures n<=5: {bad}")
check(all(eig_dim(d, 1, 1) == d for d in range(1, 8)),
      "mult_d(1) = d for d = 1..7 (unbounded as d grows: infinite on Wiener space)")
check(all(eig_dim(d, 2, 2) == comb(d + 1, 2) for d in range(1, 7)),
      "mult_d(2) = d(d+1)/2 for d = 1..6")
check(table[(2, 4)] == P[4] == 5,
      "coincidence noted: d=2, n=4 gives mult = p(4) = 5 (the law still fails at n=1,2,3)")

# ---------- 3. other readings ----------
print()
# 3a. any finite d, all n: the formula C(n+d-1, d-1) never equals p(n) for all n
for d in range(1, 30):
    first = next(n for n in range(0, 50) if comb(n + d - 1, d - 1) != P[n])
    assert first <= 2
check(True, "d = 1..29: C(n+d-1,d-1) != p(n) at some n <= 2 (n=2 for d=1, n=1 for d>=2)")
# 3b. shifted indexing mult(n) = p(n+s)
for s in (-1, 1, 2):
    ok = True
    for d in range(1, 30):
        ns = [n for n in range(max(0, -s), 60) if comb(n + d - 1, d - 1) != P[n + s]]
        ok &= len(ns) > 0
    check(ok, f"shifted reading mult(n) = p(n{s:+d}) fails for every d = 1..29")
# 3c. 'for all large n': p(n) eventually exceeds the polynomial C(n+d-1, d-1)
for d in range(1, 7):
    last_eq = max([n for n in range(0, 400) if comb(n + d - 1, d - 1) >= P[n]], default=-1)
    lower = all(P[n] >= comb(n // (d + 1) + d, d) for n in range(0, 400))
    check(last_eq < 399 and lower,
          f"d={d}: p(n) > C(n+d-1,d-1) for all 400 > n > {last_eq}; "
          f"lower bound p(n) >= C(floor(n/(d+1))+d, d) holds for n < 400")
# 3d. symmetric (S_d-invariant) eigenvectors: dimension = partitions of n into <= d parts
def sym_basis(d, n):
    """monomial symmetric polynomials m_lambda in d variables, |lambda| <= n, len <= d."""
    out = []
    for k in range(n + 1):
        for lam in partitions(k):
            if len(lam) > d:
                continue
            exps = set()
            lam_full = list(lam) + [0] * (d - len(lam))

            for perm in set(permutations(lam_full)):
                exps.add(perm)
            out.append({e: Fraction(1) for e in exps})
    return out


for d in range(1, 4):
    row = [eig_dim(d, n, n, basis=sym_basis(d, n)) for n in range(6)]
    pd = [sum(1 for lam in partitions(n) if len(lam) <= d) for n in range(6)]
    first = next(n for n in range(6) if row[n] != P[n])
    check(row == pd and first == d + 1,
          f"d={d}: S_d-symmetric eigenspaces have dims {row} = #partitions into <= {d} parts; "
          f"differs from p(n) first at n = d+1 = {first}")
# 3e. the operator that DOES have multiplicities p(n): sum_k k (d_k^2 - x_k d_k)
for d in (4, 5):
    row = [eig_dim(d, n, n, weights=list(range(1, d + 1))) for n in range(d + 1)]
    check(row == P[:d + 1],
          f"weighted operator sum_k k(d_k^2 - x_k d_k) in d={d} variables: mults {row} = p(0..{d}) "
          f"(a different operator: second quantisation of diag(1,2,3,...), not the OU operator)")

# ---------- 4. spectral counting ----------
for d in range(1, 4):
    ok = all(sum(comb(n + d - 1, d - 1) for n in range(lam + 1)) == comb(lam + d, d)
             for lam in range(30))
    check(ok, f"d={d}: counting function #{{eigenvalues <= lam}} = C(lam+d, d), a polynomial in lam")

print()
if FAIL:
    print(f"{len(FAIL)} check(s) FAILED")
    sys.exit(1)
print("ALL CHECKS PASSED")
