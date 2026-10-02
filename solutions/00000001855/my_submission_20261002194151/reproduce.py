#!/usr/bin/env python3
"""Independent verification for the disproof of conjecture 00000001855."""
import sys
from fractions import Fraction
from itertools import product

def main():
    for q in (2, 3, 4, 5):
        total = nonsing = 0
        for a, b, c in product(range(q), repeat=3):
            total += 1
            nonsing += ((a * c - b * b) % q != 0)
        exact = Fraction(nonsing, total)
        classical = Fraction(q**3 - q**2, q**3)
        formula = Fraction(q, q * q - 1)
        print(f"q={q}: exact {nonsing}/{total} = {exact}; "
              f"classical 1-1/q = {classical}; formula q/(q^2-1) = {formula}")
        assert exact == classical, "classical count mismatch"
        assert exact != formula, "formula would hold"
    print("formula wrong at n=2 for every q; direction of q-dependence also reversed")
    print("ALL CHECKS PASS — conjecture refuted")
    return 0

if __name__ == "__main__":
    sys.exit(main())
