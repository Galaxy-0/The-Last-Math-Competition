#!/usr/bin/env python3
"""Standalone recomputation for the disproof of TLMC conjecture 00000000325.

Conjecture: W(tau) = {a : liminf q^(1/tau) ||q a|| = 0} has
            packing dimension exactly 2/(1+tau).

Run:  python3 reproduce.py
No third-party dependencies (fractions/math only).
"""
from fractions import Fraction


def conjectured_dim(tau: Fraction) -> Fraction:
    """Value claimed by the conjecture: 2/(1+tau)."""
    return Fraction(2, 1 + tau)


def actual_dim(tau: Fraction) -> Fraction:
    """Packing dimension of W(tau) by the classical theory.

    Write v = 1/tau, so W(tau) = {a : for all eps>0, ||q a|| < eps q^{-v} i.m.}
    (the "exact order v" set).
      - v <= 2 (i.e. tau >= 1/2): Khinchin's theorem gives full Lebesgue
        measure, because sum_q q * (eps q^{-v}) = eps * sum_q q^{1-v} diverges
        for v <= 2.  Hence dim_P = 1.
      - v > 2 (i.e. 0 < tau < 1/2): Jarnik-Besicovitch, dim = 2/(v+1),
        and the exact-order set has the same dimension 2/(v+1) = 2 tau/(1+tau).
    """
    v = Fraction(1) / tau
    if v > 2:
        return Fraction(2, 1 + v)          # = 2*tau/(1+tau)
    return Fraction(1)


def main() -> None:
    print("=== TLMC 00000000325 : attack recomputation ===")

    # ---- Attack (primary counterexample): tau = 1/2 -----------------------
    tau = Fraction(1, 2)
    claimed = conjectured_dim(tau)
    print(f"tau = 1/2 : claimed packing dim 2/(1+tau) = {claimed}")
    # Packing dimension is monotone and dim_P(R) = 1, so no subset of R can
    # have packing dimension 4/3 > 1.  The conjecture is false outright.
    print(f"  {claimed} > 1 (ambient dimension)? {claimed > 1}")
    print(f"  cross multiplication: 4*1 > 1*3  ->  {4 * 1 > 1 * 3}")
    assert claimed == Fraction(4, 3) and claimed > 1

    # ---- Second, independent reason at the same tau -----------------------
    act = actual_dim(tau)
    print(f"  actual packing dim of W(1/2) = {act} (Khinchin: v=2, "
          f"sum q^{{1-v}} = harmonic series diverges => full measure)")
    print(f"  claimed {claimed} != actual {act}: {claimed != act}")

    # Harmonic divergence sanity check (numeric, partial sums grow w/o bound)
    s = 0.0
    for q in range(1, 200001):
        s += 1.0 / q
    print(f"  partial harmonic sum H_(2*10^5) = {s:.3f} (still growing)")

    # ---- General boundary: when is the claimed formula even admissible? ---
    print("\n tau    claimed   >1(impossible)?   actual")
    for tau in [Fraction(1, 4), Fraction(1, 3), Fraction(1, 2), Fraction(2, 3),
                Fraction(1), Fraction(3, 2), Fraction(2), Fraction(4)]:
        c, a = conjectured_dim(tau), actual_dim(tau)
        cs, as_ = str(c), str(a)
        print(f"{str(tau):>5} {cs:>9} {str(c > 1):>12}   {as_:>5}   "
              f"conjecture false: {c != a}")

    # For rational tau = p/q < 1 the claimed value 2q/(p+q) exceeds 1 iff q>p:
    p, q = 1, 2
    print(f"\nTau=p/q<1 check: 2q>p+q <=> q>p; e.g. p={p},q={q}: "
          f"{2*q > p + q}")
    # Exact-order (tau<1/2) mismatch: claimed 2/(1+tau) vs actual 2tau/(1+tau);
    # equal iff tau = 1, so the formula never holds on 0<tau<1/2 either.
    t = Fraction(1, 4)
    print(f"tau=1/4: claimed {conjectured_dim(t)} vs actual {actual_dim(t)}")


if __name__ == "__main__":
    main()
