#!/usr/bin/env python3
"""Independent recomputation for the disproof of TLMC conjecture 00000000142.

Conjecture: ESD of M_n = (1_{i+j prime})_{1<=i,j<=n} tends to the semicircle law.

Verdict: FALSE. Core identities (exact):
  tr M_n   = #{i in [1,n] : 2i prime} = 1
  tr M_n^2 = N(n) = #{(i,j) in [n]^2 : i+j prime}      (0/1 entries, symmetric)
  ESD second moment = N(n)/n ~ n/log(2n) -> infinity   (semicircle value: 1)

Usage:
  python3 reproduce.py            # pure-python trace/count core (fast)
  python3 reproduce.py --eigen    # + numpy eigvalsh spectral statistics
No absolute paths, no network. Exits nonzero if any check fails.
"""
import argparse
import math
import sys

# --- expected constants (verified independently; also fixed in Lean) ---------
RECORDED_VERDICT = {300: 0.172, 600: 0.156, 1000: 0.145}   # tr M^2 / n^2, rounded
LEAN_VALUES = {8: 23, 64: 941, 128: 3239}                  # pairCount n (Lean `decide`)
EXPECT_TR = 1                                              # tr M_n for n >= 1


def sieve(m):
    """All primes <= m."""
    s = bytearray([1]) * (m + 1)
    s[0:2] = b"\x00\x00"
    p = 2
    while p * p <= m:
        if s[p]:
            s[p * p:: p] = bytearray(len(s[p * p:: p]))
        p += 1
    return [i for i in range(2, m + 1) if s[i]]


def prime_pair_count(n, primes):
    """Exact #{(i,j) in [1,n]^2 : i+j prime} = tr M_n^2."""
    total = 0
    for p in primes:
        lo = max(1, p - n)
        hi = min(n, p - 1)
        if hi >= lo:
            total += hi - lo + 1
    return total


def tr_m(n, prime_set):
    """Exact tr M_n = #{i in [1,n] : 2i prime}."""
    return sum(1 for i in range(1, n + 1) if 2 * i in prime_set)


def core():
    primes = sieve(16000)
    prime_set = set(primes)
    ok = True

    print("== Trace identity 1: tr M_n = 1 ==")
    for n in (300, 1000, 5000):
        v = tr_m(n, prime_set)
        status = "OK" if v == EXPECT_TR else "FAIL"
        ok &= v == EXPECT_TR
        print(f"  n={n}: tr M_n = {v}  [{status}]")

    print("\n== Trace identity 2 + moment table (exact integer N(n)) ==")
    print(f"{'n':>6} {'N(n)':>10} {'N/n^2':>8} {'1/log2n':>8} {'N*log2n/n^2':>11} "
          f"{'N/n (ESD m2)':>13} {'n/log2n':>8}")
    for n in (300, 600, 1000, 2000, 4000, 8000):
        N = prime_pair_count(n, primes)
        m2 = N / n
        print(f"{n:>6} {N:>10} {N/n**2:>8.4f} {1/math.log(2*n):>8.4f} "
              f"{N*math.log(2*n)/n**2:>11.4f} {m2:>13.2f} {n/math.log(2*n):>8.2f}")
        if not (m2 > 1):
            print(f"  FAIL: ESD second moment {m2} <= 1 at n={n}")
            ok = False

    print("\n== Comparison with the recorded verdict (tr M^2/n^2) ==")
    for n, rec in RECORDED_VERDICT.items():
        v = prime_pair_count(n, primes) / n**2
        match = abs(v - rec) < 5e-4
        ok &= match
        print(f"  n={n}: recomputed {v:.4f} vs recorded {rec}  [{'OK' if match else 'FAIL'}]")

    print("\n== Cross-check with the Lean `decide` values (pairCount) ==")
    for n, expected in LEAN_VALUES.items():
        v = prime_pair_count(n, primes)
        match = v == expected
        ok &= match
        print(f"  N({n}) = {v} (Lean: {expected})  [{'OK' if match else 'FAIL'}]")

    print("\n== Growth witness (Lean moment_growth) ==")
    g = 64 * prime_pair_count(128, primes) > 128 * prime_pair_count(64, primes)
    ok &= g
    print(f"  64*N(128) > 128*N(64): {g}  [{'OK' if g else 'FAIL'}]")
    return ok


def eigen():
    try:
        import numpy as np
    except ImportError:
        print("numpy not available; skipping spectral statistics")
        return True
    print("\n== Eigenvalue statistics of the raw M_n (numpy eigvalsh) ==")
    print(f"{'n':>6} {'lmax':>9} {'lmin':>9} {'RMS=sqrt(m2)':>13} {'frac|l|<=1':>11} "
          f"{'frac l<0':>9} {'frac|l|>3':>10}")
    ok = True
    for n in (300, 600, 1000, 2000):
        is_p = np.zeros(2 * n + 1, dtype=bool)
        is_p[sieve(2 * n)] = True
        ii, jj = np.meshgrid(np.arange(1, n + 1), np.arange(1, n + 1), indexing="ij")
        M = is_p[ii + jj].astype(float)
        ev = np.linalg.eigvalsh(M)
        m2 = float((ev ** 2).mean())
        print(f"{n:>6} {ev[-1]:>9.2f} {ev[0]:>9.2f} {m2 ** 0.5:>13.2f} "
              f"{(np.abs(ev) <= 1).mean():>11.4f} {(ev < 0).mean():>9.4f} "
              f"{(np.abs(ev) > 3).mean():>10.4f}")
        ok &= abs(M.trace() - 1) < 1e-9
        ok &= abs((M @ M).trace() - prime_pair_count(n, sieve(2 * n))) < 0.5
        # semicircle: P(|l|<=1)=0.609, P(|l|>3)=0; observed: bulk escapes to +-sqrt(n/log n)
        ok &= m2 > 1
    print("  semicircle reference: m2=1, P(|l|<=1)=1/3+sqrt(3)/(2*pi)=0.609, P(|l|>3)=0")
    print("  observed: bulk spreads (RMS grows, mass outside [-3,3] grows), P(l<0)=1/2")
    return ok


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--eigen", action="store_true", help="add numpy eigvalsh statistics")
    args = ap.parse_args()
    ok = core()
    if args.eigen:
        ok &= eigen()
    print(f"\nRESULT: {'ALL CHECKS PASSED (verdict FALSE confirmed)' if ok else 'CHECKS FAILED'}")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
