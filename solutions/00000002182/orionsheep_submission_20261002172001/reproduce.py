#!/usr/bin/env python3
"""Independent verification for the disproof of conjecture 00000002182."""
import sys, math
from itertools import product

def main():
    n = 5
    total = 0
    for x in product([0, 1], repeat=n):
        f = 1 if sum(x) >= 3 else 0
        for i in range(n):
            y = list(x); y[i] ^= 1
            total += (1 if sum(y) >= 3 else 0) != f
    print(f"sensitive (input,bit) pairs = {total} / {2**n * n}")
    assert total == 60
    avg = total / 2**n
    b2 = 0.5 * math.sqrt(math.log2(5))
    be = 0.5 * math.sqrt(math.log(5))
    print(f"average sensitivity = {avg}")
    print(f"(1/2)sqrt(log2 5) = {b2};  (1/2)sqrt(ln 5) = {be}")
    assert avg > b2 and avg > be
    # squaring chain for base 2: 60/32 > ... <=> 2^225 > 5^16
    assert 2**225 > 5**16
    print(f"2^225 = {2**225} > 5^16 = {5**16}")
    print("ALL CHECKS PASS — majority-5 exceeds the conjectured supremum")
    return 0

if __name__ == "__main__":
    sys.exit(main())
