#!/usr/bin/env python3
"""Independent recomputation for the disproof of TLMC conjecture 00000000124.

Conjecture (00000000124).  Let q be an odd prime such that 2 is a primitive root
mod q; then the least positive integer m(q) missing from the orbit
{2^n mod q : n >= 0} satisfies m(q) = O((log q)^2).

Attack.  If ord_q(2) = q-1, the orbit is exactly {1, ..., q-1} (q-1 pairwise
distinct nonzero residues) and q itself (residue 0) never occurs; hence
m(q) = q identically, and q > (log q)^2 for every q >= 3.  So m(q) = q > (log q)^2
for EVERY admissible q: the conjecture fails already with constant C = 1.

This script recomputes everything from scratch (no external dependencies):
  * primality, factoring of q-1, multiplicative order of 2 (primitive-root test);
  * the full orbit {2^n mod q : 0 <= n < q-1} and the least missing positive integer;
  * the verification verdict's spot checks (q = 3 and q = 101);
  * the elementary bound (ln q)^2 < q;
  * the discrete-log witness lists used by the Lean certificates in lean4/Main.lean.
"""

import math
import sys


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    i = 3
    while i * i <= n:
        if n % i == 0:
            return False
        i += 2
    return True


def prime_factors(n: int) -> list:
    fs, d = [], 2
    while d * d <= n:
        if n % d == 0:
            fs.append(d)
            while n % d == 0:
                n //= d
        d += 1
    if n > 1:
        fs.append(n)
    return fs


def order_mod(a: int, q: int) -> int:
    """Multiplicative order of a mod q (q prime, gcd(a, q) = 1)."""
    assert pow(a, q - 1, q) == 1, "Fermat failed (q not prime?)"
    o = q - 1
    for f in set(prime_factors(q - 1)):
        while o % f == 0 and pow(a, o // f, q) == 1:
            o //= f
    return o


def is_primitive_root(a: int, q: int) -> bool:
    return order_mod(a, q) == q - 1


def orbit_set(q: int) -> set:
    return {pow(2, n, q) for n in range(q - 1)}


def least_missing(q: int) -> int:
    s = orbit_set(q)
    k = 1
    while k in s:
        k += 1
    return k


def main(bound: int = 200) -> int:
    ok = True

    print("=== 1. verdict spot checks ===")
    for q in (3, 101):
        m = least_missing(q)
        adm = is_prime(q) and is_primitive_root(2, q)
        gap = math.log(q) ** 2
        line = (f"q={q}: admissible={adm}, orbit == 1..{q-1}: {orbit_set(q) == set(range(1, q))}, "
                f"m(q)={m}, (ln q)^2={gap:.4f}, m > (ln q)^2: {m > gap}")
        print(line)
        ok &= adm and m == q and m > gap

    print(f"\n=== 2. all admissible primes (2 primitive root) below {bound} ===")
    QS = [q for q in range(3, bound, 2) if is_prime(q) and is_primitive_root(2, q)]
    print(QS)
    print(f"{'q':>4} {'ord2=q-1':>8} {'orbit=1..q-1':>12} {'m(q)':>5} {'(ln q)^2':>9} "
          f"{'m>ln^2':>7} {'m/ln^2':>7}")
    for q in QS:
        m = least_missing(q)
        checks = (order_mod(2, q) == q - 1,
                  orbit_set(q) == set(range(1, q)),
                  m == q,
                  m > math.log(q) ** 2)
        ok &= all(checks)
        print(f"{q:>4} {str(checks[0]):>8} {str(checks[1]):>12} {m:>5} "
              f"{math.log(q)**2:>9.3f} {str(checks[3]):>7} {m/math.log(q)**2:>7.2f}")
    print(f"all checks passed: {ok}")
    print("interpretation: m(q) = q for every admissible q, and q > (ln q)^2 always;")
    print("the O((log q)^2) claim fails with constant C = 1 at every admissible q.")
    print("(For an arbitrary constant C > 0: q > C (ln q)^2 for ALL q with ln q > 6C,")
    print(" so any admissible q > e^(6C) violates the bound; unboundedness of the")
    print(" admissible primes is Artin's conjecture -- true under GRH [Hooley 1967].")

    print("\n=== 3. discrete-log witnesses for the Lean certificates (lean4/Main.lean) ===")
    for q in QS:
        orb = [pow(2, n, q) for n in range(q - 1)]
        dlogs = [orb.index(k) for k in range(1, q)]
        fs = prime_factors(q - 1)
        certs = ", ".join(f"2^{(q-1)//f}%{q}={pow(2, (q-1)//f, q)}" for f in fs)
        ell = (q - 1).bit_length() - 1
        print(f"q={q}: dlogs={dlogs}")
        print(f"      pr: 2^{q-1}%{q}={pow(2, q-1, q)}, {certs}; pw: ell={ell}, ell^2={ell*ell}")

    return 0 if ok else 1


if __name__ == "__main__":
    bound = int(sys.argv[1]) if len(sys.argv) > 1 else 200
    sys.exit(main(bound))
