#!/usr/bin/env python3
"""
Standalone recomputation for the disproof of TLMC conjecture 00000000404.

Conjecture (00000000404): in the Schur expansion of the plethysm
s_{(2)}[s_{(n)}], the coefficients of "even-indexed" partitions nu are all
even (a divisibility structure).

Attack (n = 2):  s_{(2)}[s_{(2)}] = s_{(4)} + s_{(2,2)},
and the two nonzero coefficients are both exactly 1 (odd).  Under every
natural reading of "even-indexed nu" (|nu| even / all parts even / first
part even / even length) this kills the conjecture.

Method (standard library only):
  * irreducible characters chi^lam(mu) of S_m via the Murnaghan-Nakayama rule,
  * Schur functions in the power-sum basis:  s_mu = sum_rho chi^mu(rho)/z_rho p_rho,
  * plethysm through the lambda-ring identity  s_2[f] = (f*f + psi^2(f))/2,
    where psi^2 is the Adams operation p_k -> p_{2k},
  * Schur extraction by Hall orthogonality:  c_nu = sum_rho a_rho chi^nu(rho),
  * hook-content (Weyl) dimensions for the GL_4 / GL_2 cross-checks.

Run:  python3 reproduce.py
Exit code 0 iff every check passes.
"""
import sys
from fractions import Fraction
from functools import lru_cache
from collections import Counter

FAILURES = []


def check(name, cond, detail=""):
    tag = "PASS" if cond else "FAIL"
    print(f"[{tag}] {name}" + (f"  ({detail})" if detail else ""))
    if not cond:
        FAILURES.append(name)


# ----------------------------------------------------------------------
# partitions and characters
# ----------------------------------------------------------------------

def partitions(n, max_part=None):
    if max_part is None or max_part > n:
        max_part = n
    if n == 0:
        yield ()
    else:
        for first in range(min(max_part, n), 0, -1):
            for rest in partitions(n - first, min(first, n - first)):
                yield (first,) + rest


def norm(lam):
    """drop trailing zeros so (2,0) == (2,)"""
    lam = tuple(lam)
    while lam and lam[-1] == 0:
        lam = lam[:-1]
    return lam


@lru_cache(maxsize=None)
def chi(lam, mu):
    """Murnaghan-Nakayama: chi^lam(mu); lam = shape, mu = cycle-type partition."""
    lam = norm(lam)
    mu = tuple(x for x in mu if x)
    if not mu:
        return 1 if not lam else 0
    k = mu[0]
    total = 0
    for mu2 in partitions(sum(lam) - k):
        if len(mu2) > len(lam):
            continue
        if any(mu2[i] > lam[i] for i in range(len(mu2))):
            continue
        S = set()
        for i in range(len(lam)):
            lo = mu2[i] if i < len(mu2) else 0
            for j in range(lo, lam[i]):
                S.add((i, j))
        if not S:
            continue
        # edge connectivity
        start = next(iter(S))
        seen = {start}
        stack = [start]
        while stack:
            i, j = stack.pop()
            for di, dj in ((1, 0), (-1, 0), (0, 1), (0, -1)):
                c = (i + di, j + dj)
                if c in S and c not in seen:
                    seen.add(c)
                    stack.append(c)
        if len(seen) != len(S):
            continue
        # no 2x2 block
        if any((i + 1, j) in S and (i, j + 1) in S and (i + 1, j + 1) in S
               for i, j in S):
            continue
        rows = len({i for i, _ in S})
        total += (-1) ** (rows - 1) * chi(mu2, mu[1:])
    return total


def zeta(rho):
    c = Counter(rho)
    z = 1
    for k, m in c.items():
        z *= k ** m
    for m in c.values():
        z *= math_factorial(m)
    return z


def math_factorial(n):
    r = 1
    for i in range(2, n + 1):
        r *= i
    return r


def schur_to_p(mu):
    """s_mu in the power-sum basis: {rho: chi^mu(rho)/z_rho}."""
    return {rho: Fraction(chi(mu, rho), zeta(rho)) for rho in partitions(sum(mu))}


def pmul(a, b):
    """product in the power-sum basis (p_r p_s = p_{sorted(r++s)})."""
    out = {}
    for r1, c1 in a.items():
        for r2, c2 in b.items():
            key = tuple(sorted(r1 + r2, reverse=True))
            out[key] = out.get(key, Fraction(0)) + c1 * c2
    return out


def psi2(a):
    """Adams operation psi^2: p_k -> p_{2k}."""
    return {tuple(sorted((2 * x for x in rho), reverse=True)): c
            for rho, c in a.items()}


def s2_pleth(f):
    """plethysm s_2[f] = (f*f + psi^2(f)) / 2 in the power-sum basis."""
    acc = pmul(f, f)
    for k, v in psi2(f).items():
        acc[k] = acc.get(k, Fraction(0)) + v
    return {k: v / 2 for k, v in acc.items()}


def schur_coeffs(g, N):
    """Schur coefficients of the power-sum vector g at degree N
    (Hall orthogonality: c_nu = sum_rho a_rho chi^nu(rho))."""
    return {nu: sum((a * chi(nu, rho) for rho, a in g.items()), Fraction(0))
            for nu in partitions(N)}


def dim_gl(lam, d):
    """hook-content formula for dim S_lambda(C^d)."""
    tot = Fraction(1)
    for i, r in enumerate(lam):
        for j in range(r):
            arm = r - j - 1
            leg = sum(1 for i2 in range(i + 1, len(lam)) if lam[i2] > j)
            tot *= Fraction(d + (j + 1) - (i + 1), arm + leg + 1)
    return tot


# ----------------------------------------------------------------------
# C1: the S_4 character table used in lean4/Main.lean (Murnaghan-Nakayama)
#     rows: nu = (4),(31),(22),(211),(1111)
#     cols: rho = (1111),(211),(31),(22),(4)
# ----------------------------------------------------------------------
LEAN_TABLE = [
    [1, 1, 1, 1, 1],
    [3, 1, 0, -1, -1],
    [2, 0, -1, 2, 0],
    [3, -1, 0, -1, 1],
    [1, -1, 1, 1, -1],
]
ROWS = [(4,), (3, 1), (2, 2), (2, 1, 1), (1, 1, 1, 1)]
COLS = [(1, 1, 1, 1), (2, 1, 1), (3, 1), (2, 2), (4,)]
mn_table = [[chi(nu, rho) for rho in COLS] for nu in ROWS]
check("C1 S4 character table (Murnaghan-Nakayama) matches Lean table",
      mn_table == LEAN_TABLE, str(mn_table))

# ----------------------------------------------------------------------
# C2/C3: the attack at n = 2
# ----------------------------------------------------------------------
g2 = s2_pleth(schur_to_p((2,)))
expected_p = {(1, 1, 1, 1): Fraction(1, 8), (2, 1, 1): Fraction(1, 4),
              (2, 2): Fraction(3, 8), (4,): Fraction(1, 4)}
check("C2 s2[s2] power-sum expansion = (p1111+2p211+3p22+2p4)/8",
      g2 == expected_p, str({k: str(v) for k, v in sorted(g2.items())}))

coefs = schur_coeffs(g2, 4)
nz = {k: v for k, v in coefs.items() if v != 0}
check("C3 Schur expansion s2[s2] = s_(4) + s_(2,2), all other coefficients 0",
      nz == {(4,): Fraction(1), (2, 2): Fraction(1)},
      str({k: str(v) for k, v in sorted(coefs.items())}))
check("C3b c_(4) = 1 is ODD", coefs[(4,)] % 2 == 1)
check("C3c c_(2,2) = 1 is ODD", coefs[(2, 2)] % 2 == 1)

# ----------------------------------------------------------------------
# C4: every natural reading of "even-indexed nu" is refuted at n = 2
# ----------------------------------------------------------------------
readings = {
    "|nu| even": lambda v: sum(v) % 2 == 0,
    "all parts even": lambda v: all(p % 2 == 0 for p in v),
    "first part even": lambda v: v[0] % 2 == 0,
    "even length": lambda v: len(v) % 2 == 0,
}
for name, pred in readings.items():
    witnesses = {v: c for v, c in nz.items() if pred(v)}
    ok = bool(witnesses) and all(c % 2 == 1 for c in witnesses.values())
    check(f"C4 reading '{name}' has an odd-coefficient witness at n=2",
          ok, str({k: str(c) for k, c in witnesses.items()}))

# ----------------------------------------------------------------------
# C5: boundary n = 1
# ----------------------------------------------------------------------
g1 = s2_pleth(schur_to_p((1,)))
c1 = schur_coeffs(g1, 2)
check("C5 n=1: s2[s1] = s_(2) with coefficient 1 (odd)",
      c1 == {(2,): Fraction(1), (1, 1): Fraction(0)} and c1[(2,)] % 2 == 1)

# ----------------------------------------------------------------------
# C6: boundary for general n (pattern: multiplicity-free two-row even parts)
# ----------------------------------------------------------------------
pattern_ok = True
details = []
for n in range(1, 7):
    cs = schur_coeffs(s2_pleth(schur_to_p((n,))), 2 * n)
    nz = {norm(v): c for v, c in cs.items() if c != 0}
    expect = {norm((2 * n - 2 * j, 2 * j) if j else (2 * n,)): Fraction(1)
              for j in range(n // 2 + 1)}
    if nz != expect or any(c != 1 for c in nz.values()):
        pattern_ok = False
    details.append(f"n={n}:{sorted(map(str, nz))}")
check("C6 for n=1..6: s2[s_n] = sum_j s_(2n-2j,2j), every coefficient exactly 1",
      pattern_ok, " ".join(details))

# ----------------------------------------------------------------------
# C7: dimension cross-checks (Weyl / hook-content)
# ----------------------------------------------------------------------
import math
d4, d22 = dim_gl((4,), 4), dim_gl((2, 2), 4)
check("C7 GL4: dim Sym^2(Sym^2 C^4) = 55 = dim s_(4) (35) + dim s_(2,2) (20)",
      d4 == 35 and d22 == 20 and math.comb(11, 2) == 55,
      f"{d4} + {d22} = {math.comb(11, 2)}")
check("C7b GL2: dim Sym^2(Sym^2 C^2) = 6 = dim s_(4) (5) + dim s_(2,2) (1)",
      dim_gl((4,), 2) == 5 and dim_gl((2, 2), 2) == 1
      and math.comb(4, 2) == 6)

# ----------------------------------------------------------------------
print()
if FAILURES:
    print(f"RESULT: {len(FAILURES)} check(s) FAILED: {FAILURES}")
    sys.exit(1)
print("RESULT: all checks PASSED — conjecture 00000000404 is FALSE "
      "(counterexample at n = 2).")
sys.exit(0)
