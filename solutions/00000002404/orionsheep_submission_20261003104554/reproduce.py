#!/usr/bin/env python3
"""
Independent reproduction for TLMC conjecture 00000002404 (REFUTED).

Conjecture: dim J(f o g) >= max(dim J(f), dim J(g)), STRICT when f, g
are noncommuting.

Refutation: f(z) = z^2, g(z) = 3 z^2 do not commute (f o g = 9 z^4 vs
g o f = 3 z^4), but every Julia set involved is the unit circle
(z -> a z^n leaves |z| = 1 completely invariant), dimension exactly 1.
Strict inequality would demand 1 > 1.
"""

import numpy as np

# ---------- gate 1: noncommutation, symbolically and numerically ----------
# (c,d) o (e,k) = (c * e**d, d*k) for monomials c z^d, e z^k
comp = lambda f, g: (f[0] * g[0] ** f[1], f[1] * g[1])
f, g = (1, 2), (3, 2)
assert comp(f, g) == (9, 4) and comp(g, f) == (3, 4) and comp(f, g) != comp(g, f)
for z in (0.6 + 0.2j, -1.3 + 0.7j):
    fz = lambda w: w * w
    gz = lambda w: 3 * w * w
    assert abs(fz(gz(z)) - 9 * z**4) < 1e-12
    assert abs(gz(fz(z)) - 3 * z**4) < 1e-12
    assert abs(fz(gz(z)) - gz(fz(z))) > 1e-3
print("f o g = 9 z^4 != 3 z^4 = g o f — noncommuting — OK")

# ---------- gate 2: box-counting dimension of all four Julia sets ----------
# For p(z) = a z^n the filled Julia set is the disk |z| <= r, r = |a|^{-1/(n-1)},
# and J(p) is the circle |z| = r (completely invariant).  Box-count the boundary.
def box_dim_circle(a, n_pow, n=2400):
    r = abs(a) ** (-1.0 / (n_pow - 1))
    x = np.linspace(-1.2 * r, 1.2 * r, n)
    X, Y = np.meshgrid(x, x)
    F = (X**2 + Y**2) <= r * r          # filled set (analytic for monomials)
    # boundary cells: filled with a non-filled 4-neighbour
    nb = np.zeros_like(F)
    nb[1:, :] |= ~F[:-1, :]
    nb[:-1, :] |= ~F[1:, :]
    nb[:, 1:] |= ~F[:, :-1]
    nb[:, :-1] |= ~F[:, 1:]
    B = F & nb
    # box count: number of s x s blocks containing a boundary cell
    def boxes(s):
        return B.reshape(n // s, s, n // s, s).any(axis=(1, 3)).sum()
    n2, n8 = boxes(2), boxes(8)
    d = np.log(n2 / n8) / np.log(8.0 / 2.0)
    return d, r

for name, a, k in (("J(z^2)", 1.0, 2), ("J(3z^2)", 3.0, 2),
                   ("J(9z^4)", 9.0, 4), ("J(3z^4)", 3.0, 4)):
    d, r = box_dim_circle(a, k)
    assert abs(d - 1.0) < 0.15, (name, d)
    print(f"box-counting dimension of {name} (circle |z| = {r:.4f}): {d:.3f} ≈ 1 — OK")

print("all four dimensions are 1: dim J(f o g) = max(dim J(f), dim J(g)) = 1,")
print("NOT strict despite noncommutation — strict inequality would demand 1 > 1")

print("\nALL CHECKS PASSED: conjecture 00000002404 REFUTED "
      "(noncommuting pair with equal Julia dimensions, all circles)")
