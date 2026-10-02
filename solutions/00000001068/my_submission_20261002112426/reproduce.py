#!/usr/bin/env python3
"""Independent recomputation for the disproof of TLMC conjecture 00000001068.

Conjecture: the maximal sum-free subsets of F_p are exactly the intervals
((p+1)/3, 2(p-1)/3), uniquely up to dilation.

Attack: p = 11. A = {4,5,6,7} is a maximal sum-free subset of F_11 of size 4,
while the claimed interval is I = {5,6} of size 2: I is not maximal, no dilate
of I is maximal, and A is a maximal sum-free set outside the claimed family.

Run: python3 reproduce.py   (stdlib only; exits 0 iff every check passes)
"""
from itertools import combinations

P = 11
FAILS = []


def check(name, ok):
    print(("PASS " if ok else "FAIL ") + name)
    if not ok:
        FAILS.append(name)


def is_sum_free(S, p=P):
    S = set(S)
    return all((a + b) % p not in S for a in S for b in S)


# ---- core attack facts ----------------------------------------------------
A = {4, 5, 6, 7}
I = {x for x in range(P) if 3 * x > (P + 1) and 3 * x < 2 * (P - 1)}

check("A = {4,5,6,7} is sum-free in F_11", is_sum_free(A))
check("|A| = 4", len(A) == 4)
check("claimed interval I = {5,6}", I == {5, 6})
check("|I| = 2", len(I) == 2)
check("I is strictly contained in A", I < A)

AA = {(a + b) % P for a in A for b in A}
check("A + A = F_11 \\ A", AA == set(range(P)) - A)
check("A is maximal: every x outside A lies in A+A",
      all(x in AA for x in range(P) if x not in A))

# ---- dilates ---------------------------------------------------------------
dil_nonmax = True
for d in range(1, P):
    dI = {(d * x) % P for x in I}
    dA = {(d * a) % P for a in A}
    # dI has 2 elements, sits strictly inside sum-free dA  => dI not maximal
    if len(dI) != 2 or not is_sum_free(dA) or not (dI < dA):
        dil_nonmax = False
check("every nonzero dilate of I: size 2, strictly inside a sum-free dilate of A",
      dil_nonmax)
check("no dilate of I equals A (sizes 2 vs 4)",
      all({(d * x) % P for x in I} != A for d in range(1, P)))

# ---- brute-force census of F_11 (2^11 subsets) ------------------------------
all_sf = [set(c) for r in range(1, P + 1) for c in combinations(range(P), r)
          if is_sum_free(c)]
max_size = max(len(S) for S in all_sf)
maximal = [S for S in all_sf if not any(S < T for T in all_sf)]
check("maximum sum-free size in F_11 is 4", max_size == 4)
check("A is one of the 15 maximal sum-free sets",
      len(maximal) == 15 and any(S == A for S in maximal))

# ---- endpoint-convention robustness ----------------------------------------
check("integer-division open reading (4,6) = {5} is strictly inside A", {5} < A)
check("closed reading [4,6] = {4,5,6} is strictly inside A", {4, 5, 6} < A)

# ---- boundary census over small primes --------------------------------------
census_ok = True
EXPECT = {2: (0, 1), 3: (0, 1), 5: (0, 2), 7: (1, 2), 11: (2, 4), 13: (3, 4)}
for p, (i_size, m_size) in EXPECT.items():
    Ip = {x for x in range(p) if 3 * x > (p + 1) and 3 * x < 2 * (p - 1)}
    mp = max(len(S) for r in range(1, p + 1) for c in combinations(range(p), r)
             if is_sum_free(c, p) for S in [set(c)])
    if len(Ip) != i_size or mp != m_size or not (len(Ip) < mp):
        census_ok = False
check("claimed interval non-maximal for every prime p in {2,3,5,7,11,13}", census_ok)

print()
if FAILS:
    print("FAILED CHECKS:", FAILS)
    raise SystemExit(1)
print("All checks pass: conjecture 00000001068 is FALSE (counterexample p = 11).")
