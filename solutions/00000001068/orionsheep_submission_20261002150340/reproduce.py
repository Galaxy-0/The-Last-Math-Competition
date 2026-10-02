#!/usr/bin/env python3
"""Recompute every step of the disproof of TLMC conjecture 00000001068.

Conjecture: the maximal sum-free subsets of F_p are exactly the intervals
((p+1)/3, 2(p-1)/3), uniquely up to dilation.

Counterexample at p = 11: A = {4,5,6,7} is inclusion-maximal sum-free with
|A| = 4, while the conjectured interval is {5,6} (2 points), so A is not a
dilation of it.

Exit code 0 iff all checks pass.
"""

p = 11
A = {4, 5, 6, 7}

checks = []


def check(name, ok):
    checks.append(ok)
    print(f"[{'PASS' if ok else 'FAIL'}] {name}")


# 1. A is sum-free: A + A (mod 11) is disjoint from A.
AA = {(a + b) % p for a in A for b in A}
check(f"A+A = {sorted(AA)} and A + A disjoint from A", A.isdisjoint(AA))

# 2. Inclusion-maximal: every x outside A lies in A + A, so A ∪ {x} is never
#    sum-free. (A + A = F_11 \ A, so A is even a maximum sum-free set.)
comp = set(range(p)) - A
check(f"complement {sorted(comp)} subset of A+A", comp <= AA)

# 3. The conjectured interval ((p+1)/3, 2(p-1)/3) as integer points of F_11.
#    (p+1)/3 < x < 2(p-1)/3  over the rationals  <=>  p+1 < 3x < 2(p-1).
I = {x for x in range(p) if p + 1 < 3 * x < 2 * (p - 1)}
check(f"interval ((p+1)/3, 2(p-1)/3) = {sorted(I)}, size {len(I)}",
      I == {5, 6} and len(I) == 2)

# 4. No dilation of the interval equals A (exhaustive over c in F_11).
images = {tuple(sorted((c * x) % p for x in I)) for c in range(p)}
check(f"all dilation images {sorted(images)}; none equals A",
      all(set(img) != A for img in images) and all(len(set(img)) <= 2 for img in images))

# 5. Brute-force cross-check: A is a maximum-size sum-free set in F_11.
import itertools
best = max(
    r for r in range(1, p + 1)
    if any(set(S).isdisjoint({(a + b) % p for a in S for b in S})
           for S in itertools.combinations(range(p), r))
)
check(f"maximum sum-free size in F_11 is {best} (|A| = {len(A)})", best == len(A) == 4)

print()
print("ALL CHECKS PASS" if all(checks) else "SOME CHECKS FAILED")
raise SystemExit(0 if all(checks) else 1)
