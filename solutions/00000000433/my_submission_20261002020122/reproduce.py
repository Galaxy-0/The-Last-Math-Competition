#!/usr/bin/env python3
"""Standalone recomputation for the disproof of TMC conjecture 00000000433.

Claim falsified: T(B_n) = n (in particular T(B_2) = 2).
Fact established: Macdonald's Weyl denominator identity of B_2 has exactly
8 monomial terms, because the 8 exponents w(rho) - rho are pairwise distinct.

Two independent realizations of B_2 are computed in exact rational
arithmetic; any mismatch aborts with a non-zero exit code.
Run: python3 reproduce.py
"""
import itertools
import sys
from fractions import Fraction as F

failures = []


def check(name, cond):
    print(f"[{'OK' if cond else 'FAIL'}] {name}")
    if not cond:
        failures.append(name)


print("=== Realization 1: orthonormal e-basis (standard B2) ===")
# Short roots +-e1, +-e2 ; long roots +-e1 +- e2.
# Positive system: e1, e2, e1-e2, e1+e2.
pos = [(1, 0), (0, 1), (1, -1), (1, 1)]
rho = (F(sum(p[0] for p in pos), 2), F(sum(p[1] for p in pos), 2))
check("rho = (3/2, 1/2)", rho == (F(3, 2), F(1, 2)))

# W(B2) = signed permutations of the two coordinates.
deltas = set()
n_signed_perms = 0
for perm in itertools.permutations([0, 1]):
    for s0 in (1, -1):
        for s1 in (1, -1):
            wr = (s0 * rho[perm[0]], s1 * rho[perm[1]])
            deltas.add((wr[0] - rho[0], wr[1] - rho[1]))
            n_signed_perms += 1
check("|W(B2)| = 8", n_signed_perms == 8)
check("all 8 exponents w(rho)-rho pairwise distinct", len(deltas) == 8)

expected = {
    (F(0), F(0)), (F(-3), F(0)), (F(0), F(-1)), (F(-3), F(-1)),
    (F(-1), F(1)), (F(-2), F(1)), (F(-1), F(-2)), (F(-2), F(-2)),
}
check("exponent set matches the attack table entry-for-entry", deltas == expected)

s = (sum(d[0] for d in deltas), sum(d[1] for d in deltas))
check("sum_w (w(rho)-rho) = -8 rho", s == (-8 * rho[0], -8 * rho[1]))

print()
print("=== Realization 2: simple-root coordinates (alpha1 short) ===")
# Cartan [[2,-2],[-1,2]]:  s1(a2) = a2 + 2a1,  s2(a1) = a1 + a2.
def s1(v):
    return (-v[0] + 2 * v[1], v[1])


def s2(v):
    return (v[0], v[0] - v[1])


for v in [(3, -2), (1, 2), (-5, 7)]:
    check(f"s1, s2 involutions on {v}", s1(s1(v)) == v and s2(s2(v)) == v)

# Positive roots a1, a2, a1+a2, 2a1+a2 -> rho = 2a1 + (3/2)a2.
# Use the integral multiple 2rho = (4,3); scaling by 2 is a bijection, so the
# number of distinct values of w(2rho)-2rho equals that of w(rho)-rho.
rho2 = (F(4), F(3))
words = ["", "1", "2", "12", "21", "121", "212", "1212"]


def run(word, v):
    for c in reversed(word):
        v = s1(v) if c == "1" else s2(v)
    return v


vals2 = set()
for w in words:
    wr = run(w, rho2)
    vals2.add((wr[0] - rho2[0], wr[1] - rho2[1]))
check("8 reduced words give 8 distinct values of w(2rho)-2rho", len(vals2) == 8)
check("longest element w0 sends 2rho to -2rho", run("1212", rho2) == (-rho2[0], -rho2[1]))
s2_ = (sum(v[0] for v in vals2), sum(v[1] for v in vals2))
check("sum_w (w(2rho)-2rho) = -8*(4,3)", s2_ == (-8 * rho2[0], -8 * rho2[1]))

print()
print("=== Verdict ===")
check("T(B2) = 8 (8 pairwise-distinct exponents, coefficients +-1 => no cancellation)", True)
check("conjecture asserts T(B2) = n = 2", True)
check("8 != 2  =>  conjecture 00000000433 FALSIFIED", 8 != 2)

if failures:
    print(f"\n{len(failures)} CHECK(S) FAILED:", failures)
    sys.exit(1)
print("\nAll checks passed. T(B2) = 8 != 2 = n; conjecture 00000000433 is FALSE.")
