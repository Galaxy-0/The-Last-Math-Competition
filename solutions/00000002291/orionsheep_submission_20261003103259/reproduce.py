#!/usr/bin/env python3
"""
Independent reproduction for TLMC conjecture 00000002291 (REFUTED).

Conjecture: centralizers satisfy C_G(x) >= c*|G|^{1/2} with c = 1/8,
and c = 1/8 is tight, attained by low-order simple groups (e.g.
involutions of A5).

Refutation: (1) A5 attains nothing -- involutions have |C| = 4 vs
(1/8)*sqrt(60) ~ 0.97: strict slack; no centralizer order in A5 gives
equality.  (2) The bound itself fails: G = PSL(2,139), a generator of
a non-split torus has |C| = (q+1)/2 = 70, |G| = 1342740, and
64*70^2 = 313600 < 1342740.
"""

import itertools
import math

# ---------- gate 1: A5 by brute force ----------
perms = list(itertools.permutations(range(5)))
def parity(p):
    return sum(1 for i in range(5) for j in range(i + 1, 5) if p[i] > p[j]) % 2 == 0
def mul(p, q):
    return tuple(p[q[i]] for i in range(5))
A5 = [p for p in perms if parity(p)]
assert len(A5) == 60
assert len(perms) == 120
orders = {}
for x in A5:
    c = sum(1 for g in A5 if mul(g, x) == mul(x, g))
    orders.setdefault(c, 0)
    orders[c] += 1
assert set(orders) == {60, 4, 3, 5}, orders
print(f"A5: |G| = 60, centralizer orders {{|C|: #elements}} = {orders}")
for cc in sorted(orders):
    assert 64 * cc * cc != 60, cc
    assert cc / math.sqrt(60) > 1 / 8
    print(f"  |C| = {cc} ({orders[cc]} elements): ratio {cc / math.sqrt(60):.4f} > 1/8; "
          f"64*|C|^2 = {64*cc*cc} != 60")
assert 60 < 64 * 4 * 4
print("involutions: 60 < 64*16 = 1024 — bound holds with STRICT SLACK, not attained — OK")

# ---------- gate 2: |SL(2,q)| = q(q^2-1) brute-verified for small q ----------
for q2 in (3, 5, 7):
    n = sum(1 for a in range(q2) for b in range(q2)
            for cc2 in range(q2) for d in range(q2)
            if (a * d - b * cc2) % q2 == 1)
    assert n == q2 * (q2 * q2 - 1), (q2, n)
print("|SL(2,q)| = q(q^2-1) brute-verified for q = 3,5,7 — OK (formula trusted for q = 139)")

# ---------- gate 3: PSL(2,139) — explicit torus generator, bound violated ----------
q = 139
def issquare_mod(a, p):
    a %= p
    return a == 0 or pow(a, (p - 1) // 2, p) == 1
d = next(s for s in range(1, q) if not issquare_mod(s, q))
assert d == 2
def mm2(X, Y):
    (a, b), (cc, dd) = X
    (e, f), (g, h) = Y
    return ((a * e + b * g) % q, (a * f + b * h) % q), \
           ((cc * e + dd * g) % q, (cc * f + dd * h) % q)
I = (((1, 0), (0, 1)))
A = (((3, 4), (2, 3)))   # multiplication by zeta = 3 + 2u, u^2 = d = 2; det = 9 - 8 = 1
P, ordsl = I, None
for k in range(1, q * q):
    P = mm2(P, A)
    if P == I:
        ordsl = k
        break
assert ordsl == q + 1 == 140, ordsl
P = I
for _ in range(70):
    P = mm2(P, A)
assert P == (((q - 1, 0), (0, q - 1)))   # A^70 = -I
print(f"PSL(2,{q}): A = [[3,4],[2,3]] (zeta = 3+2u, u^2 = 2): order 140 in SL; "
      "A^70 = -I => image has order 70 in PSL — OK")

G = q * (q * q - 1) // 2
C = (q + 1) // 2
assert G == 1342740 and C == 70
assert 64 * C * C < G
print(f"|PSL(2,{q})| = {G}; non-split torus centralizer |C| = (q+1)/2 = {C}; "
      f"64*|C|^2 = {64*C*C} < {G} — c = 1/8 bound VIOLATED — OK")

print("\nALL CHECKS PASSED: conjecture 00000002291 REFUTED "
      "(A5 attains nothing; the c=1/8 bound fails for PSL(2,139))")
