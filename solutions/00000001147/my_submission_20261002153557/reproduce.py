#!/usr/bin/env python3
"""
Reproduce the disproof of TLMC conjecture 00000001147
("triangular H2 dimension two").

Original claim: "The dimension of the second cohomology of a triangular Lie
algebra is two; and the dimension is realized by one contribution each from
the outer derivations and the center."

Counterexample: aff(1) = 2x2 upper-triangular matrices (basis H, E,
[H,E] = E).  It is a subalgebra of triangular matrices, hence a triangular
Lie algebra under the stated definition.  We compute its Chevalley-Eilenberg
cohomology H^2 with exact rational arithmetic:

    dim H^2 (aff(1)) = 0  !=  2,

so the conjecture is false.  For contrast we also compute the 3-dimensional
Heisenberg algebra, where dim H^2 = 2 (the conjecture happens to hold there,
showing the claim is not a universal identity either way).

Usage:  python3 reproduce.py
"""

from fractions import Fraction
from itertools import combinations


def rank(rows):
    """Exact rank of an integer/Fraction matrix (list of rows)."""
    m = [[Fraction(x) for x in row] for row in rows]
    if not m:
        return 0
    ncols = len(m[0])
    r = 0
    for c in range(ncols):
        piv = next((i for i in range(r, len(m)) if m[i][c] != 0), None)
        if piv is None:
            continue
        m[r], m[piv] = m[piv], m[r]
        inv = Fraction(1) / m[r][c]
        for i in range(len(m)):
            if i != r and m[i][c] != 0:
                fac = m[i][c] * inv
                m[i] = [a - fac * b for a, b in zip(m[i], m[r])]
        r += 1
        if r == len(m):
            break
    return r


def ce_cohomology_two(dim, brackets, name):
    """
    Chevalley-Eilenberg H^2 of a Lie algebra given by structure constants.

    dim:      number of basis vectors x_0..x_{dim-1}
    brackets: {(i, j): {k: coeff}} with i < j and [x_i, x_j] = sum_k coeff*x_k
    Returns dict with dim C^1, C^2, C^3, Z^2, B^2, H^2.
    """
    lam = {k: list(combinations(range(dim), k)) for k in (1, 2, 3)}

    def bracket_vec(i, j):
        if (i, j) in brackets:
            return brackets[(i, j)]
        if (j, i) in brackets:
            return {k: -c for k, c in brackets[(j, i)].items()}
        return {}

    def wedge_coords(v, k):
        """Coordinates of omega(v, x_k) in the basis {x_a wedge x_b, a<b}."""
        out = {}
        for m, c in v.items():
            if m < k:
                out[(m, k)] = out.get((m, k), Fraction(0)) + c
            elif m > k:
                out[(k, m)] = out.get((k, m), Fraction(0)) - c
        return out

    # d : C^1 -> C^2,  (df)(x_i, x_j) = - f([x_i, x_j])
    d1 = [[Fraction(0)] * dim for _ in lam[2]]
    for r, (i, j) in enumerate(lam[2]):
        for k, c in bracket_vec(i, j).items():
            d1[r][k] -= c
    dimC1, dimC2 = dim, len(lam[2])
    dimB2 = rank(d1)

    # d : C^2 -> C^3,
    # (dw)(i,j,k) = -w([x_i,x_j],x_k) - w([x_j,x_k],x_i) - w([x_k,x_i],x_j)
    d2 = [[Fraction(0)] * dimC2 for _ in lam[3]]
    for r, (i, j, k) in enumerate(lam[3]):
        for (a, b), uv, sgn in (
            ((i, j), bracket_vec(i, j), k),
            ((j, k), bracket_vec(j, k), i),
            ((k, i), bracket_vec(k, i), j),
        ):
            for (p, q), c in wedge_coords(uv, sgn).items():
                d2[r][lam[2].index((p, q))] -= c
    dimC3 = len(lam[3])
    dimZ2 = dimC2 - rank(d2)
    dimH2 = dimZ2 - dimB2
    res = dict(C1=dimC1, C2=dimC2, C3=dimC3, Z2=dimZ2, B2=dimB2, H2=dimH2)
    print(f"{name}: " + "  ".join(f"dim {k} = {v}" for k, v in res.items()))
    return res


def main():
    print(__doc__)
    print("-" * 72)

    # aff(1): basis (H, E) = (x_0, x_1), [H, E] = E.
    aff1 = ce_cohomology_two(2, {(0, 1): {1: 1}}, "aff(1)  [H,E]=E        ")

    # 3-dimensional Heisenberg: basis (x, y, z), [x, y] = z (strictly upper
    # triangular 3x3 matrices -- also a triangular Lie algebra).
    heis = ce_cohomology_two(3, {(0, 1): {2: 1}}, "Heisenberg n3 [x,y]=z  ")

    print("-" * 72)
    assert aff1["H2"] == 0, "aff(1): expected dim H^2 = 0"
    assert heis["H2"] == 2, "Heisenberg: expected dim H^2 = 2"
    print("CONCLUSION: dim H^2(aff(1)) = 0 != 2  -> conjecture 00000001147 FALSE")
    print("(Heisenberg has dim H^2 = 2, so the value '2' is not universal either.)")


if __name__ == "__main__":
    main()
