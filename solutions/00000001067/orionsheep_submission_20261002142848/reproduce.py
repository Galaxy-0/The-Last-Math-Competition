#!/usr/bin/env python3
"""Independent recomputation for the disproof of TLMC conjecture 00000001067.

Conjecture (verbatim): "Definition: A B_h set (unique h-fold sums). Conjecture:
The maximal B2 set in F_p has size ceil(sqrt(p)) + O(1), and the O(1) term
equals 0 for p == 3 mod 4 (an exact B2 result)."

Object correspondence: a B2 set ("unique 2-fold sums") in F_p is a Sidon set of
the additive group (Z/pZ, +): a subset A such that the sums a+b (a, b in A,
a <= b, i.e. unordered pairs with repetition) are pairwise distinct modulo p.
"The maximal B2 set" = maximum cardinality M(p); the O(1) = 0 clause for
p == 3 (mod 4) asserts M(p) == ceil(sqrt(p)) exactly.

This script
  (1) exhaustively enumerates ALL k-subsets of Z/pZ for p = 11 and p = 19
      (both == 3 mod 4) and recomputes M(11) and M(19);
  (2) verifies M(11) = 3 < 4 = ceil(sqrt(11)) and M(19) = 4 < 5 = ceil(sqrt(19)),
      refuting the O(1) = 0 clause;
  (3) prints a boundary table for small primes p == 3 mod 4 using exact
      DFS backtracking (upper bound capped by the pigeonhole bound
      k(k+1)/2 <= p, so the reported maxima are exact).

Exit code 0 iff all headline assertions hold.
"""
import math
import sys
from itertools import combinations


def is_b2(S, p):
    """True iff S (a tuple of residues) is a B2 (Sidon) set of Z/pZ:
    all unordered pair sums a+b (a <= b) are distinct mod p."""
    sums = set()
    for i in range(len(S)):
        for j in range(i, len(S)):
            s = (S[i] + S[j]) % p
            if s in sums:
                return False
            sums.add(s)
    return True


def max_b2_exhaustive(p):
    """M(p) by exhaustive enumeration of ALL k-subsets for k = 1..p."""
    for k in range(1, p + 1):
        witness = None
        for S in combinations(range(p), k):
            if is_b2(S, p):
                witness = S
                break  # a k-subset exists; M(p) >= k, go on to k+1
        if witness is None:
            # no k-subset is B2; M(p) = k-1 exactly
            k1 = k - 1
            for S in combinations(range(p), k1):
                if is_b2(S, p):
                    return k1, S
            return 0, ()
        best = witness
    return p, tuple(range(p))


def max_b2_dfs(p, cap):
    """Exact M(p) by DFS backtracking (search pruned above `cap`,
    where cap exceeds the pigeonhole bound floor((sqrt(1+8p)-1)/2))."""
    bound = (math.isqrt(1 + 8 * p) - 1) // 2  # k(k+1)/2 <= p pigeonhole
    cap = min(cap, bound + 1)                 # cap > M(p), so pruning is sound
    best = 0
    sums = set()
    S = []

    def dfs(start):
        nonlocal best
        best = max(best, len(S))
        if best >= cap:
            return
        for x in range(start, p):
            # new sums when appending x: x+y for y in S (y <= x), and 2x
            new = [(x + y) % p for y in S] + [(2 * x) % p]
            if not any(v in sums for v in new):
                for v in new:
                    sums.add(v)
                S.append(x)
                dfs(x + 1)
                S.pop()
                for v in new:
                    sums.remove(v)

    dfs(0)
    return best


def main():
    ok = True

    # ---- headline attack: exhaustive over ALL subsets ------------------
    for p in (11, 19):
        m, witness = max_b2_exhaustive(p)
        cs = math.ceil(math.sqrt(p))
        status = "VIOLATES O(1)=0" if (p % 4 == 3 and m != cs) else "consistent"
        print(f"p={p:3d}  p%4={p % 4}  M(p)={m}  ceil(sqrt(p))={cs}  "
              f"witness={list(witness)}  -> {status}")
        if p == 11:
            ok &= (m == 3 and cs == 4 and p % 4 == 3)
        if p == 19:
            ok &= (m == 4 and cs == 5 and p % 4 == 3)

    # ---- boundary table (exact DFS) -------------------------------------
    print("\nboundary table, primes p == 3 mod 4 (M = exact max B2 size):")
    print("  p   p%4   M   ceil(sqrt(p))   exact?")
    for p in (3, 7, 11, 19, 23, 31, 43, 47, 59):
        m = max_b2_dfs(p, math.ceil(math.sqrt(p)) + 2)
        cs = math.ceil(math.sqrt(p))
        print(f"{p:4d} {p % 4:4d} {m:4d} {cs:8d}       "
              f"{'M = ceil(sqrt p)' if m == cs else 'M < ceil(sqrt p)'}")

    print("\nHEADLINE:", "RECOMPUTATION MATCHES ATTACK "
          "(M(11)=3<4, M(19)=4<5, both p==3 mod 4)" if ok else "MISMATCH")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
