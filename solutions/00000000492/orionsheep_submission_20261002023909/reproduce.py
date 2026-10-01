#!/usr/bin/env python3
"""Standalone recomputation of the disproof of TLMC conjecture 00000000492.

Conjecture (as stated): the expectation of the multiset of hook lengths of a
uniformly random standard tableau, normalized, equals (n^2 - 1)/3:
    (sum of hooks)/n^2 = (n^2 - 1)/3     (alternative reading: /(n) instead of /n^2)

Fact used (shape-only): the multiset of hook lengths depends only on the shape,
so the "expectation over uniform random standard tableaux" is a constant per shape.

This script needs only the Python standard library.
Run:  python3 reproduce.py
"""

from fractions import Fraction


def hooks_of_shape(shape):
    """Hook lengths of a Young diagram given as a list of row lengths."""
    rows = len(shape)
    H = {}
    for i in range(rows):
        for j in range(shape[i]):
            right = shape[i] - j - 1
            below = sum(1 for r in range(rows) if r > i and shape[r] > j)
            H[(i, j)] = right + below + 1
    return H


def num_std_tableaux(shape):
    """Number of standard Young tableaux of the shape, via the hook length formula."""
    H = hooks_of_shape(shape)
    n = sum(shape)
    f = 1
    for h in H.values():
        f *= h
    # n! / product(hooks)
    fact = 1
    for k in range(2, n + 1):
        fact *= k
    assert fact % f == 0
    return fact // f


def main():
    ok = True

    print("== Universal cap (reading n cells, divide by n^2) ==")
    print("Each hook length of an n-cell tableau is <= n (a hook is the cell plus at")
    print("most n-1 cells strictly right/below), so sum(hooks) <= n^2 and")
    print("(sum/n^2) <= 1.  The conjectured value (n^2-1)/3 exceeds 1 for every n >= 3.")
    for n in range(3, 8):
        cap = Fraction(1)
        conj = Fraction(n * n - 1, 3)
        print(f"  n={n}: cap = 1, conjectured = {conj}, conjectured > cap: {conj > cap}")
        ok &= conj > cap

    print()
    print("== Concrete counterexample, n = 3 cells, row shape (3) ==")
    H = hooks_of_shape([3])
    s = sum(H.values())
    print(f"  hooks = {sorted(H.values(), reverse=True)}, sum = {s}")
    print(f"  unique standard tableau (count = {num_std_tableaux([3])}), so expectation = {s}")
    lhs = Fraction(s, 9)
    rhs = Fraction(3 * 3 - 1, 3)
    print(f"  (sum)/n^2 = {s}/9 = {lhs}   vs   conjectured (n^2-1)/3 = (3^2-1)/3 = {rhs}")
    print(f"  equal? {lhs == rhs}")
    ok &= lhs != rhs

    print()
    print("== Concrete counterexample, square reading: 3x3 square (n^2 = 9 cells) ==")
    H = hooks_of_shape([3, 3, 3])
    s = sum(H.values())
    print(f"  hooks = {sorted(H.values(), reverse=True)}")
    print(f"  sum = {s}  (equals n^3 = 27 for an n x n square)")
    lhs = Fraction(s, 9)
    rhs = Fraction(9 - 1, 3)
    print(f"  (sum)/n^2 = {s}/9 = {lhs}   vs   conjectured {rhs};  equal? {lhs == rhs}")
    ok &= lhs != rhs
    print("  Solve n = (n^2-1)/3  <=>  n^2 - 3n - 1 = 0: discriminant 13, not a")
    print("  perfect square, so no integer n works; the square reading fails for all n.")

    print()
    print("== Concrete counterexample, divide-by-n reading ==")
    H = hooks_of_shape([3])
    s = sum(H.values())
    lhs = Fraction(s, 3)
    rhs = Fraction(9 - 1, 3)
    print(f"  n=3: (sum)/n = {s}/3 = {lhs} vs conjectured {rhs}; equal? {lhs == rhs}")
    ok &= lhs != rhs
    H = hooks_of_shape([4])
    s = sum(H.values())
    lhs = Fraction(s, 4)
    rhs = Fraction(16 - 1, 3)
    print(f"  n=4: (sum)/n = {s}/4 = {lhs} vs conjectured {rhs}; equal? {lhs == rhs}")
    print("  Cap: sum/n <= n, and (n^2-1)/3 > n for n >= 4 (n^2-3n-1 > 0).")
    ok &= lhs != rhs

    print()
    print("== Expectation over uniform random tableaux, shape (2,1), n = 3 cells ==")
    shape = [2, 1]
    cnt = num_std_tableaux(shape)
    H = hooks_of_shape(shape)
    s = sum(H.values())
    print(f"  shape (2,1): {cnt} standard tableaux, hook multiset {sorted(H.values(), reverse=True)}")
    print(f"  (identical for every tableau), E[sum] = {s}")
    print(f"  E[sum]/n^2 = {Fraction(s, 9)} vs 8/3; E[sum]/n = {Fraction(s, 3)} vs 8/3")
    ok &= Fraction(s, 9) != Fraction(8, 3) and Fraction(s, 3) != Fraction(8, 3)

    print()
    print("VERDICT:", "FALSE confirmed - all checks consistent" if ok else "INCONSISTENCY")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
