#!/usr/bin/env python3
"""Independent verification for the disproof of conjecture 00000001465.

For f(x) = |x| (L(f) = 1, claimed lambda* = 1) and lambda = 4 > 1:
M_4(h) = h^2/8 for |h| <= 4 (exact quadratic formula, certified by the
lower bound 8|y| + (h-y)^2 >= h^2 with equality iff y = h/2's prox...),
in particular M_4(0) = 0 attained uniquely at the minimizer y = 0 of f,
and the envelope is differentiable at the minimizer (quotient h/8 -> 0).
The claimed "nondifferentiable at a minimizer for lambda > lambda*"
fails; there is no critical parameter for convex f.
Exit 0 iff all checks pass.
"""
from fractions import Fraction as F
import sys


def env(h, lam=4):
    """Moreau envelope M_lam(|.|)(h) = inf_y |y| + (h-y)^2/(2*lam),
    computed exactly with the closed form: soft-threshold prox."""
    t = F(2 * lam)
    a = F(h)
    # prox of |.| at h: sign(h)*max(|h|-lam, 0)
    if a > lam:
        y = a - lam
    elif a < -lam:
        y = a + lam
    else:
        y = F(0)
    return abs(y) + F((h - y) ** 2, 2 * lam)


def main():
    lam = 4
    # exact envelope values near the minimizer
    for h in (0, 1, 2, 3, 4):
        v = env(h, lam)
        assert v == F(h * h, 8), (h, v)
        print(f"M_4({h}) = {v} = h^2/8 — OK")
    assert env(0, lam) == 0

    # differentiability at the minimizer 0: for |h| <= lambda = 4 the
    # envelope is exactly h^2/8, so the difference quotients are h/8 -> 0
    for h in (1, 2, 3, 4):
        q = float(env(h, lam) / h)
        print(f"  quotient (M(h)-M(0))/h at h = {h}: {q:.6f}")
        assert abs(q - float(h) / 8) < 1e-12
        assert q <= 0.5
    print("quotients h/8 -> 0: differentiable at the minimizer x = 0 — OK")

    # symmetric left-side check (even function)
    for h in (1, 2, 3, 4):
        assert env(-h, lam) == env(h, lam)
    print("even symmetry — OK")

    # the claimed lambda*: L(|.|) = 1; instance lambda = 4 > 1
    assert 4 > 1
    print("lambda = 4 > lambda* = 1 yet the envelope is C^1 — clause refuted")

    print("ALL CHECKS PASS — no nondifferentiability at the minimizer")
    return 0


if __name__ == "__main__":
    sys.exit(main())
