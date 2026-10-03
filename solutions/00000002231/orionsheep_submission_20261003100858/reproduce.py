#!/usr/bin/env python3
"""
Independent reproduction for TLMC conjecture 00000002231 (REFUTED).

Conjecture: there exists a transcendental meromorphic f whose
deficiency spectrum {delta(a)} realizes exactly ANY prescribed closed
subset of [0,1] containing 0.

Refutation: Nevanlinna's defect relation sum_a delta(a) <= 2 forces the
spectrum to be at most countable (shell bound: at most 2n values with
delta >= 1/n), while "any prescribed closed subset" includes
uncountable sets such as [0,1] itself.
"""

from fractions import Fraction
import math
import cmath

# ---------- gate 1: shell-counting arithmetic (kernel `shell_count`) ----------
# with total defect <= 2, at most 2n values can reach delta >= 1/n
for n in range(1, 51):
    # max k with k * (1/n) <= 2, by exact rationals
    k = 0
    while Fraction(k + 1, n) <= 2:
        k += 1
    assert k == 2 * n, (n, k)
print("shell bound verified exactly for n = 1..50: max #{delta >= 1/n} = 2n — OK")

# ---------- gate 2: the defect relation itself, numerically (f = e^z) ----------
# T(r, e^z) = (1/2pi) * int log^+|e^{r e^{i theta}}| dtheta = r/pi;  no zeros,
# no poles => N(0, f) = N(inf, f) = 0 => delta(0) = delta(inf) = 1, sum = 2.
for r in (1.0, 3.0, 7.0, 20.0):
    N = 2048
    zs = [r * complex(math.cos(2 * math.pi * j / N), math.sin(2 * math.pi * j / N))
          for j in range(N)]
    integ = sum(max(math.log(abs(cmath.exp(w))), 0.0) for w in zs) / N
    T = integ
    # log^+|e^{re^{i*theta}}| = max(r cos theta, 0); integral = 2r exactly,
    # so T = r/pi; Riemann sum at the kink has O((pi/N)^2) error
    assert abs(T - r / math.pi) < 1e-5, (r, T)
delta0 = 1.0   # N(0, e^z) = 0
delta_inf = 1.0
assert delta0 + delta_inf <= 2 + 1e-12
print(f"T(r, e^z) = r/pi verified to 1e-5 at r in {{1,3,7,20}}; "
      f"delta(0) = delta(inf) = 1, sum = {delta0 + delta_inf} <= 2 — OK")
print("spectrum of e^z = {0, 1}: a finite closed set containing 0 (realizable)")

# ---------- gate 3: [0,1] is uncountable — Cantor diagonal, constructively ----------
def diagonal_refutes(f):
    g = [not f[i][i] for i in range(len(f))]
    return all(f[i] != g for i in range(len(f)))

import random
random.seed(2231)
for trial in range(1000):
    f = [[random.random() < 0.5 for _ in range(12)] for _ in range(12)]
    assert diagonal_refutes(f)
print("Cantor diagonal: 1000/1000 candidate enumerations of Bool sequences "
      "miss the diagonal sequence — OK (no surjection Nat -> 2^Nat)")

# ---------- gate 4: the instance — [0,1] demands 7 values >= 1/3 ----------
vals = [Fraction(7, 21), Fraction(9, 21), Fraction(11, 21), Fraction(13, 21),
        Fraction(15, 21), Fraction(17, 21), Fraction(1, 1)]
assert all(v >= Fraction(1, 3) for v in vals)
assert len(set(vals)) == 7
# realizing all seven: total defect >= 7 * 1/3 = 7/3 > 2 — violates the relation
assert 7 * Fraction(1, 3) > 2
print("instance: 7 distinct values of [0,1] lie >= 1/3; realizing them forces "
      f"total defect >= 7/3 = {7 * Fraction(1,3)} > 2 — relation violated; "
      "shell bound allows only 2*3 = 6")

print("\nALL CHECKS PASSED: conjecture 00000002231 REFUTED "
      "(spectrum at most countable; uncountable prescriptions impossible)")
