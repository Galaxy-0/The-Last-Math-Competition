#!/usr/bin/env python3
"""Independent verification for the disproof of conjecture 00000003797.

f(x) = x^2, gradient 2x, spectral interval [2,2], midpoint 2: with the
claimed optimal step h = 2 the projected gradient iteration is
x_{n+1} = -3 x_n: magnitudes 3^n |x_0| diverge (3^10 = 59049 > 10^4).
With the true optimal step h = 1/2 the iteration converges in one step.
Exit 0 iff all checks pass.
"""
import sys


def main():
    x = 1.0
    for n in range(1, 11):
        x = -3.0 * x
        print(f"n = {n}: x_n = {x:.1f} (|x_n| = {abs(x):.1f})")
    assert abs(x) > 10 ** 4
    print("iteration with the claimed optimal step diverges")

    # contrast: true optimal step 1/2 for x^2 converges in one step
    x = 1.0
    x = x - 0.5 * (2 * x)
    assert x == 0.0
    print("with the true optimal step 1/2: one-step convergence to 0")

    print("ALL CHECKS PASS — spectral midpoint 2 is a divergent step")
    return 0


if __name__ == "__main__":
    sys.exit(main())
