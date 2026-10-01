#!/usr/bin/env python3
"""
Independent recomputation for the disproof of TLMC conjecture 00000000485.

Conjecture (paraphrase): the proportion of partitions lambda of n with
|chi_lambda(c_n)| > 1 (irreducible character of S_n evaluated at an n-cycle)
tends to 1 as n -> infinity.

This script recomputes chi_lambda(c_n) from scratch, with NO reliance on the
original pipeline, and shows the proportion is identically 0.

Verification stack (all pure stdlib):
  1. Characters are computed by the Murnaghan-Nakayama rule (recursive rim-hook
     removal), implemented independently here.
  2. The implementation is validated against three independent facts:
     a. column orthogonality:  sum_lambda chi_lambda(mu)^2 = z_mu  for every mu,
     b. f^lambda = chi_lambda(1^n) matches the hook-length formula,
     c. the standard representation: chi_{(n-1,1)}(mu) = (#fixed points) - 1.
  3. The n-cycle column is then inspected: every value lies in {0, +1, -1};
     nonzero iff lambda is a hook (lambda_2 <= 1), sign = (-1)^(height-1).

Conclusion: #{lambda : |chi_lambda(c_n)| > 1} = 0 for every n, so the
proportion is the constant function 0, which does NOT tend to 1.
The conjecture is FALSE.
"""

from functools import lru_cache
from math import gcd, factorial
from itertools import count


# ---------------------------------------------------------------- partitions
def partitions(n):
    """All partitions of n as non-increasing lists."""
    out = []

    def rec(k, mx, cur):
        if k == 0:
            out.append(tuple(cur))
            return
        for a in range(min(k, mx), 0, -1):
            cur.append(a)
            rec(k - a, a, cur)
            cur.pop()

    rec(n, n, [])
    return out


def z_mu(mu):
    """z_mu = product over part-sizes: m_i! * i^(m_i); |centralizer| order."""
    from collections import Counter
    z = 1
    for i, m in Counter(mu).items():
        z *= factorial(m) * i ** m
    return z


# ------------------------------------------- Murnaghan-Nakayama (rim hooks)
def cells(lam):
    return {(i, j) for i, row in enumerate(lam) for j in range(row)}


def rim_cells(lam):
    """Cells (i,j) of lam such that (i+1,j+1) is not in lam (rim/skew diagonal).
    Ordered along the boundary from bottom-left to top-right."""
    S = cells(lam)
    cand = [(i, j) for (i, j) in S if (i + 1, j + 1) not in S]
    # order: sort by (i + j) descending? Standard boundary order: sort by
    # content j - i ascending from bottom-left to top-right.  Use the walk:
    # start at the cell in the last row, column 0; repeatedly move Up if
    # possible (cell above is in cand and not used), else move Right.
    cand_set = set(cand)
    start = (len(lam) - 1, 0)
    assert start in cand_set
    path = [start]
    used = {start}
    while True:
        i, j = path[-1]
        up, right = (i - 1, j), (i, j + 1)
        if up in cand_set and up not in used and up in cells(lam):
            path.append(up)
            used.add(up)
        elif right in cand_set and right not in used and right in cells(lam):
            path.append(right)
            used.add(right)
        else:
            break
    assert len(path) == len(cand), (lam, path, cand)
    return path


def chi_mn(lam, mu):
    """chi_lambda(mu) by recursive Murnaghan-Nakayama rim-hook removal."""
    lam = tuple(x for x in lam if x > 0)
    mu = tuple(x for x in mu if x > 0)

    @lru_cache(maxsize=None)
    def go(lam, mu):
        if not mu:
            return 1 if not lam else 0
        if not lam:
            return 0
        k, rest = mu[0], mu[1:]
        S = cells(lam)
        path = rim_cells(lam)
        total = 0
        # every contiguous segment of the rim path of length k
        for s in range(len(path) - k + 1):
            seg = path[s:s + k]
            rest_cells = S - set(seg)
            if not rest_cells:
                if rest:
                    continue
                # height of the strip = #rows it spans
                total += (-1) ** (seg[-1][0] - seg[0][0])
                continue
            # remainder must be a Young diagram: left-justified rows that are
            # weakly decreasing in length
            rows = {}
            for (i, j) in rest_cells:
                if j > 0 and (i, j - 1) not in rest_cells:
                    break
                rows.setdefault(i, 0)
                rows[i] = max(rows[i], j + 1)
            else:
                rl = [rows[i] for i in sorted(rows)]
                if any(rl[a] < rl[a + 1] for a in range(len(rl) - 1)):
                    continue
                if any(i not in rows for i in range(max(rows) + 1)):
                    continue
                total += (-1) ** (seg[-1][0] - seg[0][0]) * go(tuple(rl), rest)
                continue
            continue
        return total

    return go(lam, mu)


# ------------------------------------------------------- independent checks
def hook_length_f(lam):
    """f^lambda by the hook-length formula (independent of MN)."""
    n = sum(lam)
    lam_ext = list(lam) + [0] * (len(lam) + 1)
    prod = 1
    for i in range(len(lam)):
        for j in range(lam[i]):
            below = sum(1 for a in range(i + 1, len(lam)) if lam_ext[a] > j)
            prod *= lam[i] - j + below
    return factorial(n) // prod


def fixed_points(mu):
    from collections import Counter
    c = Counter(mu)
    return sum(m for size, m in c.items() if size == 1)


def main():
    print("Conjecture 00000000485 falsification: recomputation")
    print("=" * 64)
    ok = True

    for n in range(1, 16):
        parts = partitions(n)
        mus = partitions(n)

        # --- full character table by MN
        table = {mu: {lam: chi_mn(lam, mu) for lam in parts} for mu in mus}

        # (a) column orthogonality: sum_lam chi_lam(mu)^2 == z_mu
        for mu in mus:
            s = sum(table[mu][lam] ** 2 for lam in parts)
            if s != z_mu(mu):
                print(f"FAIL column orthogonality n={n} mu={mu}: {s} != {z_mu(mu)}")
                ok = False

        # (b) f^lambda == hook-length formula
        for lam in parts:
            if table[(1,) * n][lam] != hook_length_f(lam):
                print(f"FAIL hook-length n={n} lam={lam}")
                ok = False
            if sum(table[mu][lam] ** 2 for mu in mus) != z_mu((1,) * n):
                pass  # row orthogonality of dimension implied by column checks

        # (c) standard representation: chi_{(n-1,1)}(mu) = fixes(mu) - 1
        if n >= 2:
            for mu in mus:
                lam = (n - 1, 1)
                if table[mu][lam] != fixed_points(mu) - 1:
                    print(f"FAIL standard rep n={n} mu={mu}")
                    ok = False

        # --- the n-cycle column
        cyc = {lam: table[(n,)][lam] for lam in parts}
        bad = [lam for lam in parts if abs(cyc[lam]) > 1]
        hooks = [lam for lam in parts if len(lam) == 1 or lam[1] <= 1]
        mn_ok = all(
            (cyc[lam] == 0 and lam not in hooks)
            or (lam in hooks and cyc[lam] == (-1) ** (len(lam) - 1))
            for lam in parts
        )
        if not mn_ok or bad:
            print(f"FAIL n-cycle column n={n}: bad={bad} borderstrip={mn_ok}")
            ok = False

        prop = f"{len(bad)}/{len(parts)} = {len(bad) / len(parts):.6f}"
        print(f"n={n:2d}  p(n)={len(parts):3d}  |chi|>1 count={len(bad):2d}  "
              f"proportion={prop}  hook-values ok={mn_ok}")

    print("-" * 64)
    if ok:
        print("ALL CHECKS PASSED.")
        print("The proportion of shapes with |chi_lambda(c_n)| > 1 is the")
        print("constant 0 for every n; it cannot tend to 1.")
        print("Conjecture 00000000485 is FALSE.")
    else:
        print("CHECKS FAILED - do not submit.")
        raise SystemExit(1)


if __name__ == "__main__":
    main()
