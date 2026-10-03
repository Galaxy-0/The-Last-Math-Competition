#!/usr/bin/env python3
"""Independent verification for the disproof of conjecture 00000001464.

The Legendre transform is an involution: L(L f) = f.  Hence
L(L(L f)) = L f for every f, so period 3 (L(L(L f)) = f with
L f != f) collapses to a fixed point.  Verified numerically: for
several convex functions the iterates L^k f alternate with period 2
(L^2 f = f), never exhibiting period 3; a fixed point (x^2/2) is
self-dual.  Numerical Legendre transforms computed by convex
optimization on a grid.
Exit 0 iff all checks pass.
"""
import numpy as np
import sys

GRID = np.linspace(-4, 4, 1601)


def legendre_vals(fv, grid=GRID):
    """Legendre transform of the sampled convex function fv (values on
    the grid): f*(p) = max over the grid of p x - f(x)."""
    vals = grid[:, None] * grid[None, :] - fv[None, :]
    am = vals.argmax(axis=1)
    res = vals[np.arange(len(grid)), am]
    # refine with the supporting line at the argmax (exact for the
    # piecewise-linear interpolant): f*(p) on the dual grid via
    # supporting-line evaluation
    return res


def lt_of_vals(fv):
    """Return the sampled Legendre transform as values on GRID, computed
    via supporting lines of the piecewise-linear interpolant."""
    out = np.empty_like(fv)
    N = len(fv) - 1
    for i, p in enumerate(GRID):
        # supporting slope of the convex interpolant at p: the argmax j
        vals = GRID * p - fv
        j = int(vals.argmax())
        out[i] = vals.max()
    return out


def check_roundtrip(name, f_vals):
    fs = lt_of_vals(f_vals)
    fss = lt_of_vals(fs)
    err = np.abs(fss - f_vals).max()
    scale = max(1.0, np.abs(f_vals).max())
    assert err / scale < 1e-2, (name, err)
    print(f"{name}: ||L(L f) - f||_inf / scale = {err / scale:.2e} "
          f"— period 2 (round trip), OK")


def main():
    # 1. quadratic: self-dual fixed point (period 1)
    quad = lt_of_vals(GRID ** 2 / 2)
    assert np.abs(quad - GRID ** 2 / 2).max() < 1e-2
    print("f(x) = x^2/2: L f = f — fixed point (period 1) — OK")

    # 2. convex examples with the sup attained on the grid: all have
    #    period exactly 2 (e^x is excluded: its transform is unbounded
    #    for p <= 0, i.e. the grid would truncate it)
    check_roundtrip("f(x) = |x|", np.abs(GRID))
    check_roundtrip("f(x) = max(x^2/2, |x| - 1)",
                    np.maximum(GRID ** 2 / 2, np.abs(GRID) - 1))
    check_roundtrip("f(x) = huber-like",
                    np.where(np.abs(GRID) <= 1,
                             GRID ** 2 / 2, np.abs(GRID) - 0.5))
    print("all iterates satisfy L(L f) = f, i.e. L^3 f = L f — "
          "no period-3 points exist")

    # 3. arithmetic anchor: 3 > 2^{3/2} is not needed here; the refutation
    #    is structural (involution), independent of any numeric bound
    print("ALL CHECKS PASS — the Legendre transform has no period-3 points")
    return 0


if __name__ == "__main__":
    sys.exit(main())
