#!/usr/bin/env python3
"""
Independent recomputation for the disproof of TLMC conjecture 00000001040.

Conjecture: at q = 2 (mod 3), the complete-mapping polynomials (f with f+x a
permutation) form exactly the equivalence class of x^3 type.

Counterexample: q = 5 (prime, 5 = 2 mod 3).
  * f(x) = 2x is a complete mapping (2x and 3x are both permutations);
  * the entire affine x^3-family {A(x+B)^3 + C} contains NO complete mapping,
    so the x^3-type class is empty at q = 5;
  * hence the complete mappings (15 of them, all linear) are NOT the x^3 class.

No third-party dependencies. Exits 0 iff all checks pass.
"""

P = 5


def perm_on_f5(values):
    """True iff `values` (5 residues of Z_5) are pairwise distinct, i.e. the
    induced function on F_5 is a bijection."""
    return sorted(values) == list(range(P))


def perm(poly):
    return perm_on_f5([poly(x) % P for x in range(P)])


def is_complete_mapping(f):
    """f is a complete mapping iff f and f+x are both permutations."""
    return perm(f) and perm(lambda x, f=f: (f(x) + x) % P)


def main():
    checks = []

    # -- Check 0: q = 5 is admissible (prime, 5 = 2 mod 3) -------------------
    checks.append(("q=5 satisfies 5 % 3 == 2", 5 % 3 == 2))

    # -- Check 1: f(x) = 2x is a complete mapping ----------------------------
    two_x = [(2 * x) % 5 for x in range(5)]
    three_x = [(3 * x) % 5 for x in range(5)]
    checks.append(("2x is a permutation [0,2,4,1,3]", two_x == [0, 2, 4, 1, 3] and perm_on_f5(two_x)))
    checks.append(("3x = 2x + x is a permutation [0,3,1,4,2]", three_x == [0, 3, 1, 4, 2] and perm_on_f5(three_x)))

    # -- Check 2: x^3 + x is not a permutation; 0, 2, 3 collide at 0 ---------
    cube_vals = [((x ** 3) + x) % 5 for x in range(5)]
    collisions = [x for x in range(5) if cube_vals[x] == 0]
    checks.append(("x^3+x not a permutation", not perm_on_f5(cube_vals)))
    checks.append(("x^3+x sends 0, 2, 3 all to 0", collisions == [0, 2, 3]))

    # -- Check 3: the whole affine x^3-family has no complete mapping --------
    # f = A(x+B)^3 + C  =>  f + x = A*y^3 + y + (C-B) with y = x+B,
    # so f is a complete mapping iff A*y^3 + y is a permutation (C irrelevant).
    no_cube_cm = True
    detail = {}
    for A in range(1, 5):  # A in F_5^x
        for B in range(5):
            f = lambda x, A=A, B=B: (A * (((x + B) % 5) ** 3)) % 5
            if is_complete_mapping(f):
                no_cube_cm = False
        detail[A] = [(A * y ** 3 + y) % 5 for y in range(5)]
    checks.append(("no A(x+B)^3 (A!=0, B in F_5) is a complete mapping", no_cube_cm))
    for A, vals in detail.items():
        checks.append((f"A={A}: A*y^3+y = {vals} not a permutation", not perm_on_f5(vals)))

    # -- Check 4: exactly 15 linear complete mappings, a in {1,2,3} ----------
    linear_cms = [
        (a, b)
        for a in range(5)
        for b in range(5)
        if is_complete_mapping(lambda x, a=a, b=b: (a * x + b) % 5)
    ]
    checks.append(("exactly 15 linear complete mappings", len(linear_cms) == 15))
    checks.append(("their slopes are a in {1,2,3}", sorted(set(a for a, _ in linear_cms)) == [1, 2, 3]))

    # -- Check 5: brute force over ALL permutations of F_5 -------------------
    # Every function F_5 -> F_5 is a polynomial of degree < 5, so counting over
    # permutations g (with g + id a permutation) counts all complete mappings.
    import itertools

    total = sum(
        1
        for g in itertools.permutations(range(5))
        if perm_on_f5([(g[x] + x) % 5 for x in range(5)])
    )
    checks.append(("Z_5 has exactly 15 complete mappings in total", total == 15))
    checks.append(("all of them are linear (x^3 class contributes 0)", total == len(linear_cms)))

    ok = True
    for name, passed in checks:
        print(("PASS" if passed else "FAIL"), "-", name)
        ok = ok and passed
    print()
    print("VERDICT: conjecture 00000001040 is", "DISPROVED at q=5" if ok else "NOT DISPROVED")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
