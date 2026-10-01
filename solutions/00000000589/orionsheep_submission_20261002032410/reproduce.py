#!/usr/bin/env python3
"""
Independent recomputation for the disproof of TLMC conjecture 00000000589.

Conjecture (00000000589): for every 3-generated numerical semigroup S = <a,b,c>,
    g(S) <= sqrt(3) * (abc)^(1/3) * (1 + o(1)),
and the constant sqrt(3) is optimal (Erdos-Graham type), where g(S) is the
Frobenius number (largest non-representable non-negative integer).

Attack family:  S_n = <n, n+1, n^2 - n - 1>  (n >= 3).
Claim (verified here by brute force AND proved in main.tex):
    g(S_n) = n^2 - 2n - 1  exactly, for all n >= 3,
so that
    g(S_n) / (sqrt(3) * (abc)^(1/3))  ~  n^(2/3) / sqrt(3)  ->  infinity.
Hence the bound sqrt(3)*(abc)^(1/3) fails, and fails by an unbounded factor.

Run:  python3 reproduce.py
No third-party dependencies.
"""

import math

def frobenius_bruteforce(a, b, c):
    """Largest non-representable integer of <a,b,c>, by dynamic programming.

    Upper bound used: gcd(a,b) = 1 here, so g(<a,b,c>) <= g(<a,b>) = ab - a - b
    (adding generators can only shrink the Frobenius number)."""
    assert math.gcd(math.gcd(a, b), c) == 1, "Frobenius number undefined"
    upper = a * b - a - b
    reach = [False] * (upper + 1)
    reach[0] = True
    for m in range(1, upper + 1):
        for g in (a, b, c):
            if m >= g and reach[m - g]:
                reach[m] = True
                break
    gaps = [m for m in range(upper + 1) if not reach[m]]
    assert gaps, "cofinite with conductor 0 (trivial semigroup)"
    return max(gaps)

def family_gens(n):
    return (n, n + 1, n * n - n - 1)

def formula_g(n):
    return n * n - 2 * n - 1

def ratio(n):
    a, b, c = family_gens(n)
    return formula_g(n) / (math.sqrt(3) * (a * b * c) ** (1 / 3))

def main():
    ok = True

    print("== 1. Brute-force enumeration vs. exact formula g = n^2 - 2n - 1 ==")
    print("   (independent DP enumeration; bound ab-a-b = g(<n,n+1>) used only as")
    print("    an upper cutoff, never as the answer)")
    for n in (3, 4, 5, 6, 8, 12, 20):
        a, b, c = family_gens(n)
        gbf = frobenius_bruteforce(a, b, c)
        gf = formula_g(n)
        match = "OK" if gbf == gf else "MISMATCH"
        ok &= (gbf == gf)
        print(f"   n={n:>3}: <{a},{b},{c}>  brute={gbf:>6}  formula={gf:>6}  [{match}]")
    print("   full sweep n = 3 .. 60:")
    bad = [n for n in range(3, 61)
           if frobenius_bruteforce(*family_gens(n)) != formula_g(n)]
    print("   mismatches:", bad if bad else "none")
    ok &= not bad

    print()
    print("== 2. Ratio g / (sqrt(3)*(abc)^(1/3)) along the attack family ==")
    print("   (verdict quoted values: n=6 -> 1.244, n=20 -> 3.824)")
    for n in (6, 20):
        a, b, c = family_gens(n)
        print(f"   n={n:>3}: g={formula_g(n)}, abc={a*b*c}, "
              f"sqrt(3)*(abc)^(1/3)={math.sqrt(3)*(a*b*c)**(1/3):.6f}, "
              f"ratio={ratio(n):.6f}")

    print()
    print("== 3. Where does the claimed sqrt(3) bound first fail? ==")
    first = next(n for n in range(3, 200) if ratio(n) > 1.0)
    for n in range(3, first + 2):
        print(f"   n={n}: ratio={ratio(n):.6f}  {'VIOLATION' if ratio(n) > 1 else 'holds'}")
    print(f"   first violation: n = {first}  (g = {formula_g(first)} > "
          f"{math.sqrt(3)*(family_gens(first)[0]*family_gens(first)[1]*family_gens(first)[2])**(1/3):.6f} "
          f"= sqrt(3)*(abc)^(1/3))")
    ok &= (first == 6)

    print()
    print("== 4. Divergence: ratio ~ n^(2/3)/sqrt(3) -> infinity ==")
    for n in (6, 20, 100, 1000, 10**6):
        print(f"   n={n:>9}: ratio={ratio(n):12.6f}   "
              f"n^(2/3)/sqrt(3)={n**(2/3)/math.sqrt(3):12.6f}")
    print("   => no constant C can rescue the bound g <= C*(abc)^(1/3) on this family;")
    print("      in particular the constant sqrt(3) is not merely suboptimal: no finite")
    print("      constant works, so 'sqrt(3) is optimal' is false a fortiori.")

    print()
    print("== 5. Boundary behaviour ==")
    print("   n = 2: c = 1, semigroup <2,3,1> contains 1: trivial, g undefined.")
    print("   n = 3,4,5: bound still holds (ratios "
          f"{ratio(3):.4f}, {ratio(4):.4f}, {ratio(5):.4f}).")
    print(f"   n = 6: first violation (ratio {ratio(6):.4f}).")

    print()
    print("ALL CHECKS PASSED" if ok else "SOME CHECK FAILED")
    return 0 if ok else 1

if __name__ == "__main__":
    raise SystemExit(main())
