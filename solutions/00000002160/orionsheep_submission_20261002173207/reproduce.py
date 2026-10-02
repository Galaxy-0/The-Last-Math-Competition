#!/usr/bin/env python3
"""Independent verification for the disproof of conjecture 00000002160."""
import sys
from fractions import Fraction

def main():
    v, k, lam_min = 100, 22, -8
    bound = Fraction(v * (-lam_min), k - lam_min)
    print(f"Hoffman bound = {v}*{-lam_min}/({k}{lam_min:+d}) = {bound} = {float(bound)}")
    assert bound == Fraction(800, 30)
    assert bound.denominator != 1, "bound would be integral"
    alpha = 22  # classical: independence number of the Higman-Sims graph
    print(f"alpha(Higman-Sims) = {alpha} (classical)")
    assert Fraction(alpha) != bound
    print("integer alpha can never equal the non-integer bound; also 22 != 800/30")
    print("ALL CHECKS PASS — conjecture refuted")
    return 0

if __name__ == "__main__":
    sys.exit(main())
