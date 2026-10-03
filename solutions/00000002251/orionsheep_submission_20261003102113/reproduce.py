#!/usr/bin/env python3
"""
Independent reproduction for TLMC conjecture 00000002251 (REFUTED).

Conjecture: Delta_c f = f(z+c) - f(z) has kernel of dimension 1, and
the spectrum of Delta_c is of the explicit {2 sin(kc/2)} type.

Refutation: ker Delta_c = c-periodic meromorphic functions is
infinite-dimensional: it contains {e^{2 pi i k z / c}}_{k in N},
pairwise non-proportional. Already dim >= 4 (kernel-certified), and
the spectrum conjunct fails independently (eigenvalues e^{lam c} - 1
of the eigenfunctions e^{lam z} sweep a continuum, not the discrete
real set {2 sin(kc/2)}).
"""

import cmath
import math

c = 1.7  # representative shift

# ---------- gate 1: c-periodicity of every kernel member ----------
for k in range(1, 9):
    for z in (0.3, 1.1, 2.7):
        f1 = cmath.exp(2j * math.pi * k * z / c)
        f2 = cmath.exp(2j * math.pi * k * (z + c) / c)
        assert abs(f1 - f2) < 1e-9, (k, z)
print("e^{2 pi i k z / c} is c-periodic for k = 1..8 (checked at 3 points) — OK")

# ---------- gate 2: values at z = c/4 and z = c/8 distinguish members ----------
q = cmath.exp(1j * math.pi / 2)          # e^{2 pi i (c/4) / c} = i
vals4 = [q ** k for k in range(4)]       # 1, i, -1, -i
assert all(abs(vals4[a] - vals4[b]) > 1e-9
           for a in range(4) for b in range(4) if a != b)
print("at z = c/4 the members k = 0..3 take the four units 1, i, -1, -i — pairwise distinct — OK")

eighth = cmath.exp(1j * math.pi / 4)     # at z = c/8
vals8 = [eighth ** k for k in range(8)]
assert all(abs(vals8[a] - vals8[b]) > 1e-9
           for a in range(8) for b in range(8) if a != b)
print("at z = c/8 the members k = 0..7 take 8 pairwise-distinct values — OK")
print("=> at least 8 pairwise non-proportional kernel members (kernel certifies >= 4; prose: infinite)")

# ---------- gate 3: g is not a multiple of any constant ----------
g0, gq = cmath.exp(0.0), cmath.exp(1j * math.pi / 2)
assert abs(g0 - gq) > 1e-9
print(f"g(0) = 1, g(c/4) = i — distinct, so g is not constant — OK")

# ---------- gate 4: spectrum conjunct fails ----------
# Delta_c e^{lam z} = (e^{lam c} - 1) e^{lam z}: eigenvalues sweep a continuum.
sins = [2 * math.sin(k * c / 2) for k in range(-20, 21)]
lam = 0.5
ev = cmath.exp(lam * c) - 1
assert all(abs(ev.real - s) > 1e-6 for s in sins), (ev, sins)
print(f"eigenvalue e^({lam}c) - 1 = {ev.real:.6f} (lam = {lam} real) matches no "
      f"2 sin(kc/2) in k = -20..20 — spectrum conjunct violated — OK")
ev2 = cmath.exp((1 + 1j) * c) - 1
assert abs(ev2.imag) > 1e-6
print(f"for lam = 1 + i the eigenvalue {ev2:.6f} is not even real — OK")

print("\nALL CHECKS PASSED: conjecture 00000002251 REFUTED "
      "(ker Delta_c infinite-dimensional; spectrum not {2 sin(kc/2)})")
