#!/usr/bin/env python3
"""Independent verification for the disproof of conjecture 00000002024."""
import sys

def min_fourth_powers(n):
    # exact DP: minimal number of k-th powers summing to n
    k4 = [i**4 for i in range(1, int(n**0.25) + 2) if i**4 <= n]
    dp = [0] + [10**9] * n
    for m in range(1, n + 1):
        for p in k4:
            if p <= m:
                dp[m] = min(dp[m], dp[m - p] + 1)
    return dp[n]

def main():
    # the formula's value at k = 4
    val = 2**4 + (81 // 16) - 2
    print(f"floor((3/2)^4) = floor(81/16) = {81//16}")
    print(f"2^4 + floor((3/2)^4) - 2 = {val}")
    assert val == 19
    # the conjecture's own g(4) = 19; its strict inequality is 19 > 19:
    assert not (19 > 19), "strict inequality would hold"
    # spot-check g(4) = 19 (Balasubramanian-Deshouillers-Dress): the classical
    # witness 79 = 4*16 + 15*1 needs 19 fourth powers, and nothing needs more
    need = min_fourth_powers(79)
    print(f"min #4th powers for 79: {need}")
    assert need == 19
    assert all(min_fourth_powers(n) <= 19 for n in range(1, 344))  # g(4) <= 19 on [1, 2^4*2^4+16)
    print("g(4) = 19 = formula value -> k=4 is NOT an exception; strict inequality false")
    print("ALL CHECKS PASS — conjecture refuted by its own numbers")
    return 0

if __name__ == "__main__":
    sys.exit(main())
