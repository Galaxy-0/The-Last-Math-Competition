#!/usr/bin/env python3
"""Independent recomputation for the disproof of TLMC conjecture 00000000405.

Conjecture: for every partition lambda of n,
    K_{lambda,(1^n)} * K_{lambda',(1^n)}  divides  n!.

Counterexample found: n = 3, lambda = (2,1):
    K_{(2,1),(1^3)} = 2 (SYT count, hook formula: 3!/(3*1*1))
    (2,1) is self-conjugate, so K_{(2,1)',(1^3)} = 2
    product 4, 3! = 6, 6 mod 4 = 2 != 0  ->  4 does not divide 6.

No third-party dependencies. Kostka numbers are recomputed from scratch by
brute-force enumeration of semistandard Young tableaux (rows weakly increasing,
columns strictly increasing downward), cross-checked with the hook-length formula.
Run: python3 reproduce.py
"""
from math import factorial
from itertools import product as iproduct


def partitions(n, maxpart=None):
    """All partitions of n as tuples of positive integers, decreasing."""
    if maxpart is None or maxpart > n:
        maxpart = n
    if n == 0:
        yield ()
        return
    for first in range(maxpart, 0, -1):
        for rest in partitions(n - first, min(first, n - first) if n - first else 0):
            yield (first,) + rest


def conjugate(lam):
    if not lam:
        return ()
    return tuple(sum(1 for x in lam if x >= j) for j in range(1, lam[0] + 1))


def hook_formula(lam):
    """Number of SYT of shape lam (hook-length formula)."""
    conj = conjugate(lam)
    prod = 1
    for i, row in enumerate(lam):          # i: 0-indexed row
        for j in range(1, row + 1):        # j: 1-indexed column
            hook = (row - j) + (conj[j - 1] - i - 1) + 1
            prod *= hook
    return factorial(sum(lam)) // prod


def ssyt_count(lam, mu):
    """K_{lam,mu}: brute-force count of SSYT of shape lam, content mu.

    Depth-first construction of the filling cell by cell (rows left-to-right,
    top-to-bottom), pruning as soon as a partial filling violates semistandardness
    (rows weakly increasing, columns strictly increasing downward) or the content
    budget of any symbol is exceeded.
    """
    cells = [(i, j) for i, row in enumerate(lam) for j in range(row)]
    k = len(mu)
    remaining = list(mu)

    def rec(idx, grid):
        if idx == len(cells):
            return 1
        i, j = cells[idx]
        lo = 1
        if j > 0:
            lo = max(lo, grid[(i, j - 1)])        # row weakly increasing
        if i > 0:
            lo = max(lo, grid[(i - 1, j)] + 1)    # column strictly increasing downward
        total = 0
        for v in range(lo, k + 1):
            if remaining[v - 1] > 0:
                remaining[v - 1] -= 1
                grid[(i, j)] = v
                total += rec(idx + 1, grid)
                remaining[v - 1] += 1
        return total

    return rec(0, {})


def list_syt(lam):
    """Explicit list of standard tableaux of shape lam (content (1^n))."""
    cells = [(i, j) for i, row in enumerate(lam) for j in range(row)]
    out = []
    for filling in iproduct(range(1, len(cells) + 1), repeat=len(cells)):
        if sorted(filling) != list(range(1, len(cells) + 1)):
            continue
        grid = dict(zip(cells, filling))
        rows_ok = all(grid[(i, j)] < grid[(i, j + 1)]
                      for (i, j) in cells if (i, j + 1) in grid)
        cols_ok = all(grid[(i, j)] < grid[(i + 1, j)]
                      for (i, j) in cells if (i + 1, j) in grid)
        if rows_ok and cols_ok:
            out.append(filling)
    return out


def main():
    print("=" * 72)
    print("Counterexample: n = 3, lambda = (2,1)")
    print("=" * 72)
    lam = (2, 1)
    n = 3
    lam_c = conjugate(lam)
    print(f"lambda = {lam}, lambda' = {lam_c}, self-conjugate: {lam_c == lam}")
    syt = list_syt(lam)
    print(f"SYT of shape (2,1) (row-major entries): {syt}  -> f = {len(syt)}")
    one_n = (1,) * n
    K = ssyt_count(lam, one_n)
    Kc = ssyt_count(lam_c, one_n)
    fh = hook_formula(lam)
    print(f"K_(lam,(1^n))   brute force = {K}, hook formula = {fh}, agree: {K == fh == 2}")
    print(f"K_(lam',(1^n))  brute force = {Kc} (self-conjugate)")
    prod = K * Kc
    print(f"product = {K}*{Kc} = {prod}")
    print(f"3! = {factorial(3)}, remainder {factorial(3)} mod {prod} = {factorial(3) % prod}")
    verdict = factorial(3) % prod == 0
    print(f"divides 3! : {verdict}")
    assert prod == 4 and not verdict, "counterexample must be 4 not dividing 6"
    print("=> CONJECTURE 00000000405 IS FALSE")

    print()
    print("=" * 72)
    print("Boundary sweep n <= 12 (correct divisibility: n! mod (K*K') == 0)")
    print("=" * 72)
    first_bad = None
    for n in range(1, 13):
        viol = []
        for lam in partitions(n):
            one_n = (1,) * n
            K = ssyt_count(lam, one_n)
            Kc = ssyt_count(conjugate(lam), one_n)
            if factorial(n) % (K * Kc) != 0:
                viol.append((lam, K, Kc))
        if viol and first_bad is None:
            first_bad = (n, viol)
        if n <= 5 or viol:
            status = f"{len(viol)} violation(s): {viol}" if viol else "all shapes OK"
            print(f"n = {n:2d}: {status}")
    assert first_bad == (3, [((2, 1), 2, 2)]), "minimal counterexample must be n=3, (2,1)"
    print()
    print(f"Minimal counterexample: n = {first_bad[0]}, lambda = {first_bad[1][0][0]}")
    print("All assertions passed. Recomputation matches the submitted disproof.")


if __name__ == "__main__":
    main()
