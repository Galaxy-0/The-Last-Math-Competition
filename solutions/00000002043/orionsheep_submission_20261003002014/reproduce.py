#!/usr/bin/env python3
"""Independent verification for the disproof of conjecture 00000002043.

1. s_q digit sums from scratch: s_3(3n) = s_3(n) for EVERY n (zero trit
   appended), checked for all n < 10^6.
2. The count #{n in [0, x) : s_3(3n) = s_3(n)} equals x exactly for
   x = 10^1 .. 10^6 (linear).
3. The ratio count / (x/sqrt(log x)) diverges: no constant c fits the
   claimed asymptotic.
Exit 0 iff all checks pass.
"""
import sys
from math import log2, isqrt


def s3(n):
    """Base-3 digit sum."""
    t = 0
    while n:
        t += n % 3
        n //= 3
    return t


def main():
    # (1) the identity, exhaustively up to 10^6
    N = 10 ** 6
    for n in range(N):
        if s3(3 * n) != s3(n):
            print(f"FAIL: s3(3*{n}) != s3({n})")
            return 1
    print(f"identity s3(3n) = s3(n): holds for all n < {N}")

    # (2) the count is exactly linear
    for e in range(1, 7):
        x = 10 ** e
        c = sum(1 for n in range(x) if s3(3 * n) == s3(n))
        print(f"x = 10^{e}: count = {c} (x = {x})")
        assert c == x, f"count {c} != {x}"

    # (3) ratio to the claimed shape diverges
    print("ratio count / (x / sqrt(log2 x)):")
    prev = 0.0
    for e in range(1, 7):
        x = 10 ** e
        r = x / (x / (log2(x) ** 0.5))
        print(f"  x = 10^{e}: {r:.3f}")
        assert r > prev
        prev = r

    print("ALL CHECKS PASS — count is exactly linear, asymptotic is false")
    return 0


if __name__ == "__main__":
    sys.exit(main())
