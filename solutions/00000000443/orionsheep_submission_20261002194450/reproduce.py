#!/usr/bin/env python3
"""Independent verification for the disproof of conjecture 00000000443."""
import sys, math

# Mobius function for n <= 12 (factorization table)
def mobius(n):
    fac = {4: 0, 8: 0, 9: 0, 12: 0, 1: 1, 2: -1, 3: -1, 5: -1, 6: 1,
           7: -1, 10: 1, 11: -1}
    return fac[n]

def witt(n, k=2):
    return sum(mobius(d) * k ** (n // d) for d in range(1, n + 1)
               if n % d == 0) // n

def main():
    bad = []
    for n in range(2, 13):
        dim = witt(n)
        bound = 2 ** (n - 1) - 2 ** math.ceil(n / 2)
        print(f"n={n}: dim L_n = {dim}, bound = {bound}, holds? {dim >= bound}")
        if dim < bound:
            bad.append(n)
    assert 5 in bad
    print(f"violations at n = {bad}; in particular n=5: 6 >= 8 is false")
    print("ALL CHECKS PASS — conjecture refuted")
    return 0

if __name__ == "__main__":
    sys.exit(main())
