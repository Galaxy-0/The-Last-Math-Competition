#!/usr/bin/env python3
"""Independent exact arithmetic sanity check; no crossing number is computed."""
from fractions import Fraction
from math import floor, prod


def z(m, n):
    # Rational floors give the displayed mathematical expression directly.
    return prod(floor(Fraction(k, 2)) for k in (m, m - 1, n, n - 1))


def main():
    factors = [floor(Fraction(k, 2)) for k in (7, 6, 7, 6)]
    value = z(7, 7)
    assert factors == [3, 3, 3, 3]
    assert value == 81
    assert value != 77
    assert min(7, 7) <= 7
    print("Formula factors at (7,7):", factors)
    print("Z(7,7) =", value)
    print("Z(7,7) != 77; min(7,7) <= 7")
    print("Thus the asserted formula range forces cr(7,7)=81, contradicting cr(7,7)=77.")
    print("No crossing-number value was computed or assumed.")
    print("ALL CHECKS PASSED")


if __name__ == "__main__":
    main()
