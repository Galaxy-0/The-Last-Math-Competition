#!/usr/bin/env python3
"""Standalone recomputation for the disproof of conjecture 00000000348.

Conjecture: exists alpha whose continued-fraction partial quotients satisfy
a_n = a_{n+1} = floor(tau(n)) for all n >= 1, with tau the divisor function.

Attack: n = 4 forces a_5 = tau(4); n = 5 forces a_5 = tau(5).
tau(4) = 3 and tau(5) = 2 give a_5 = 3 and a_5 = 2 -- contradiction.
Run: python3 reproduce.py
"""


def tau(n: int) -> int:
    """Divisor function: number of positive divisors of n."""
    return sum(1 for d in range(1, n + 1) if n % d == 0)


def main() -> None:
    print("tau values:")
    for n in range(1, 7):
        divs = [d for d in range(1, n + 1) if n % d == 0]
        print(f"  tau({n}) = {tau(n)}  divisors = {divs}")

    t4, t5 = tau(4), tau(5)
    print(f"\nn=4 forces: a_4 = a_5 = floor(tau(4)) = {t4}")
    print(f"n=5 forces: a_5 = a_6 = floor(tau(5)) = {t5}")
    print(f"-> a_5 must equal both {t4} and {t5}")

    assert t4 == 3, f"tau(4) expected 3, got {t4}"
    assert t5 == 2, f"tau(5) expected 2, got {t5}"
    assert t4 != t5, "expected tau(4) != tau(5)"

    # Extra boundary check: conflict already at a_2 via n = 1, 2.
    t1, t2 = tau(1), tau(2)
    assert t1 == 1 and t2 == 2 and t1 != t2

    print("\nCONFIRMED: conjecture 00000000348 is FALSE "
          "(no alpha can satisfy the overlapping constraints).")


if __name__ == "__main__":
    main()
