#!/usr/bin/env python3
"""Independent verification for the disproof of conjecture 00000002142."""
import sys

def srg_identity(v, k, lam, mu):
    return k * (k - lam - 1) == (v - k - 1) * mu

def main():
    lhs = 153 * (153 - 32 - 1)
    rhs = (460 - 153 - 1) * 57
    print(f"153*(153-32-1) = {lhs}")
    print(f"(460-153-1)*57 = {rhs}")
    assert lhs == 18360 and rhs == 17442
    assert lhs != rhs, "identity would hold"
    # sanity: the identity holds on classical feasible parameter sets
    for (v, k, lam, mu) in [(5, 2, 0, 1), (16, 5, 0, 2), (16, 6, 2, 2),
                            (10, 3, 0, 1), (25, 8, 3, 2), (460, 153, 32, 57)]:
        print(f"SRG({v},{k},{lam},{mu}): identity {srg_identity(v,k,lam,mu)}")
    assert srg_identity(5, 2, 0, 1) and srg_identity(16, 5, 0, 2)
    assert not srg_identity(460, 153, 32, 57)
    print("No SRG(460,153,32,57) exists -> no cospectral mates -> conjecture refuted")
    return 0

if __name__ == "__main__":
    sys.exit(main())
