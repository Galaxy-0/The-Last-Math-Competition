#!/usr/bin/env python3
"""
Independent reproduction for TLMC conjecture 00000002341 (REFUTED).

Conjecture: pseudospectral area = pi*eps^2*(1 + ||A*A - AA*||_HS/2),
area growth exactly eps^2.

Refutation: A = diag(0,10) is normal (deviation 0) so the claim
predicts pi*eps^2, but the true eps-pseudospectrum of a normal matrix
is the union of eps-disks around each eigenvalue: 2*pi*eps^2 here.
And for the nilpotent Jordan block J_n the area scales like
eps^{2/n}, not eps^2.
"""

import numpy as np

# ---------- gate 1: exact normal instance A = diag(0,10) ----------
A = np.diag([0.0, 10.0])
dev = np.linalg.norm(A.conj().T @ A - A @ A.conj().T)
assert dev == 0.0
claimed_factor = 1 + dev / 2
actual_factor = 2      # two disjoint eps-disks
assert 2 * 1 < 10
print(f"A = diag(0,10): ||A*A - AA*||_HS = {dev}; claimed factor = {claimed_factor}; "
      f"actual = {actual_factor} (two disjoint eps-disks)")

def area_grid(M, eps, n=900, re=(-2.0, 12.0), im=(-2.0, 2.0)):
    rex = np.linspace(re[0], re[1], n)
    imx = np.linspace(im[0], im[1], n)
    area = 0.0
    cell = (rex[1] - rex[0]) * (imx[1] - imx[0])
    for x in rex:
        for y in imx:
            z = complex(x, y)
            Minv = np.linalg.inv(M - z * np.eye(M.shape[0]))
            if np.linalg.norm(Minv, 2) > 1 / eps:
                area += cell
    return area

# resolution-scaled check for eps=1 on diag(0,10): analytic 2*pi
for eps, n in ((1.0, 500),):
    ar = area_grid(A, eps, n=n)
    exact = 2 * np.pi * eps ** 2
    claimed = np.pi * eps ** 2
    print(f"eps={eps}: grid area = {ar:.4f} (analytic 2*pi*eps^2 = {exact:.4f}; "
          f"claimed pi*eps^2 = {claimed:.4f})")
    assert abs(ar - exact) < 0.25 * exact
    assert abs(claimed - exact) > 1.0

# ---------- gate 2: growth clause — nilpotent Jordan J_4 ----------
def jordan(n):
    return np.diag(np.ones(n - 1), 1)

J = jordan(4)
a1 = area_grid(J, 0.2, n=600)
a2 = area_grid(J, 0.05, n=600)
ratio = a1 / a2
print(f"J_4: area(eps=0.2)/area(eps=0.05) = {ratio:.2f}")
print(f"eps^2 growth predicts (0.2/0.05)^2 = 16; eps^{2/4} growth predicts "
      f"{(0.2/0.05)**0.5:.2f}")
assert ratio < 16 * 0.7   # clearly not eps^2 growth
print("growth is far from eps^2 for non-normal J_4 — OK")

print("\nALL CHECKS PASSED: conjecture 00000002341 REFUTED "
      "(normal diag(0,10): claimed pi*eps^2 vs actual 2*pi*eps^2; "
      "J_4 area growth ~ eps^{1/2}, not eps^2)")
