"""Independent checks for conjecture 00000000438 (Python 3 standard library only).

NSym = Q<S_1, S_2, ...> (noncommutative symmetric functions), graded by deg S_k = k,
with the coproduct  Delta S_k = sum_{i+j=k} S_i (x) S_j  (S_0 = 1), extended
multiplicatively.  The degree-n part has basis S^I = S_{i1}...S_{il}, I a composition of n.

We compute dim P_n, P_n = {x in NSym_n : Delta x = x(x)1 + 1(x)x}, for n = 1..10 by
three different methods:
  (1) directly, as the kernel of x -> Delta x - x(x)1 - 1(x)x (exact rational rank for
      n <= 8, rank modulo the prime 2^61 - 1 for n <= 10);
  (2) by duality: the S-basis is dual to the monomial basis M_I of QSym, whose
      product is the quasi-shuffle; P_n is the annihilator of the decomposables
      (QSym_+)^2 in degree n, so dim P_n = 2^(n-1) - rank(products M_a M_b) (n <= 7);
  (3) by the Milnor-Moore / PBW identity  prod_k (1 - t^k)^(-p_k) = (1 - t)/(1 - 2t),
      solved for p_k recursively (NSym = U(P), Hilbert series (1-t)/(1-2t)).
Eulerian numbers A(n,1) are computed by brute force over permutations (n <= 9) and by
the closed formula (n <= 10), for all conventions (descents/ascents, 0- or 1-based).
The degree-3 computation (the decisive case) is printed in detail.
"""

from fractions import Fraction
from itertools import permutations
from math import comb


def comps(n):
    if n == 0:
        return [()]
    out = []
    for i in range(1, n + 1):
        for c in comps(n - i):
            out.append((i,) + c)
    return out


def rank(rows):
    M = [[Fraction(x) for x in r] for r in rows if any(r)]
    r = 0
    ncols = len(M[0]) if M else 0
    for c in range(ncols):
        p = next((i for i in range(r, len(M)) if M[i][c] != 0), None)
        if p is None:
            continue
        M[r], M[p] = M[p], M[r]
        for i in range(len(M)):
            if i != r and M[i][c] != 0:
                f = M[i][c] / M[r][c]
                M[i] = [x - f * y for x, y in zip(M[i], M[r])]
        r += 1
    return r


# ---------- method (1): coproduct kernel ----------
def coprod_S(I):
    """Delta S^I as dict (J, K) -> coefficient, via the multiplicative extension."""
    res = {((), ()): 1}
    for i in I:
        new = {}
        for (J, K), c in res.items():
            for a in range(i + 1):
                key = (J + ((a,) if a else ()), K + ((i - a,) if i - a else ()))
                new[key] = new.get(key, 0) + c
        res = new
    return res


def reduced(I):
    d = coprod_S(I)
    d[(I, ())] -= 1
    d[((), I)] -= 1
    return {k: v for k, v in d.items() if v}


def dim_prim_direct(n):
    basis = comps(n)
    red = [reduced(I) for I in basis]
    keys = sorted({k for r in red for k in r})
    if not keys:
        return len(basis)
    M = [[r.get(k, 0) for r in red] for k in keys]
    return len(basis) - rank(M)


P = 2 ** 61 - 1


def rank_modp(rows):
    M = [[x % P for x in r] for r in rows if any(r)]
    r = 0
    ncols = len(M[0]) if M else 0
    for c in range(ncols):
        p = next((i for i in range(r, len(M)) if M[i][c]), None)
        if p is None:
            continue
        M[r], M[p] = M[p], M[r]
        inv = pow(M[r][c], P - 2, P)
        M[r] = [x * inv % P for x in M[r]]
        for i in range(len(M)):
            if i != r and M[i][c]:
                f = M[i][c]
                M[i] = [(x - f * y) % P for x, y in zip(M[i], M[r])]
        r += 1
    return r


def dim_prim_direct_modp(n):
    basis = comps(n)
    red = [reduced(I) for I in basis]
    keys = sorted({k for r in red for k in r})
    if not keys:
        return len(basis)
    # rows indexed by basis elements (transpose; same rank)
    M = [[r.get(k, 0) for k in keys] for r in red]
    return len(basis) - rank_modp(M)


# ---------- method (2): duality with QSym ----------
def quasi_shuffle(a, b):
    """M_a * M_b in QSym, as dict composition -> coefficient."""
    if not a:
        return {b: 1}
    if not b:
        return {a: 1}
    out = {}
    for w, c in quasi_shuffle(a[1:], b).items():
        k = (a[0],) + w
        out[k] = out.get(k, 0) + c
    for w, c in quasi_shuffle(a, b[1:]).items():
        k = (b[0],) + w
        out[k] = out.get(k, 0) + c
    for w, c in quasi_shuffle(a[1:], b[1:]).items():
        k = (a[0] + b[0],) + w
        out[k] = out.get(k, 0) + c
    return out


def dim_prim_dual(n):
    basis = comps(n)
    idx = {I: j for j, I in enumerate(basis)}
    rows = []
    for k in range(1, n):
        for a in comps(k):
            for b in comps(n - k):
                row = [0] * len(basis)
                for w, c in quasi_shuffle(a, b).items():
                    row[idx[w]] += c
                rows.append(row)
    return len(basis) - (rank(rows) if rows else 0)


# ---------- method (3): Hilbert series ----------
def dims_pbw(N):
    # coefficients of (1-t)/(1-2t): 1, 1, 2, 4, 8, ...
    target = [1] + [2 ** (n - 1) for n in range(1, N + 1)]
    p = [0] * (N + 1)
    for n in range(1, N + 1):
        # series of prod_{k<n} (1-t^k)^(-p_k), coefficient of t^n
        s = [1] + [0] * N
        for k in range(1, n):
            for _ in range(p[k]):
                # multiply by 1/(1-t^k)
                for m in range(k, N + 1):
                    s[m] += s[m - k]
        p[n] = target[n] - s[n]  # (1-t^n)^(-p_n) contributes p_n t^n
    return p[1:]


# ---------- Eulerian numbers ----------
def euler_formula(n, k):  # number of permutations of [n] with k descents
    return sum((-1) ** j * comb(n + 1, j) * (k + 1 - j) ** n for j in range(k + 2))


def euler_brute(n):
    des = [0] * (n + 1)
    asc = [0] * (n + 1)
    for p in permutations(range(1, n + 1)):
        d = sum(1 for i in range(n - 1) if p[i] > p[i + 1])
        des[d] += 1
        asc[n - 1 - d] += 1
    return des, asc


def main():
    ok = True
    # degree-3 details
    print("degree 3 basis:", comps(3))
    for I in comps(3):
        print("  reduced coproduct of S^%s:" % (I,), dict(sorted(reduced(I).items())))
    psi3 = {(3,): 3, (2, 1): -1, (1, 2): -2, (1, 1, 1): 1}
    comm = {(2, 1): 1, (1, 2): -1}
    for name, x in (("Psi_3", psi3), ("[S_2,S_1]", comm)):
        tot = {}
        for I, c in x.items():
            for k, v in reduced(I).items():
                tot[k] = tot.get(k, 0) + c * v
        prim = all(v == 0 for v in tot.values())
        print("  %s primitive: %s" % (name, prim))
        ok &= prim
    N = 10
    Nd = 8
    d1 = [dim_prim_direct(n) for n in range(1, Nd + 1)]
    print("dim P_n (direct kernel over Q), n=1..%d:" % Nd, d1)
    dp = [dim_prim_direct_modp(n) for n in range(1, N + 1)]
    print("dim P_n (direct kernel mod p),  n=1..%d:" % N, dp)
    d2 = [dim_prim_dual(n) for n in range(1, 8)]
    print("dim P_n (QSym duality),         n=1..7:", d2)
    d3 = dims_pbw(N)
    print("dim P_n (Hilbert series),       n=1..%d:" % N, d3)
    # rank mod p <= rank over Q, so dim over Q <= dim mod p; the Hilbert-series
    # values are exact, and all three agree.
    ok &= d1 == d3[:Nd] and d2 == d3[:7] and dp == d3
    ok &= d3[2] == 2
    d1 = d3
    # Eulerian numbers
    A0 = [euler_formula(n, 1) for n in range(1, N + 1)]
    A1 = [euler_formula(n, 0) for n in range(1, N + 1)]
    print("A(n,1), 0-based (perms with 1 descent),  n=1..%d:" % N, A0)
    print("A(n,1), 1-based (perms with 1 run),      n=1..%d:" % N, A1)
    for n in range(1, 10):
        des, asc = euler_brute(n)
        ok &= des == [euler_formula(n, k) for k in range(n + 1)]
        ok &= asc == des  # ascents and descents are equidistributed
        ok &= des[1] == A0[n - 1] and des[0] == A1[n - 1] == 1
    ok &= all(A0[n - 1] == 2 ** n - n - 1 for n in range(1, N + 1))
    print("brute force over permutations agrees with the formula for n <= 9")
    some = [n for n in range(1, N + 1) if d1[n - 1] != A0[n - 1] or d1[n - 1] != A1[n - 1]]
    both = [n for n in range(1, N + 1) if d1[n - 1] != A0[n - 1] and d1[n - 1] != A1[n - 1]]
    print("n in 1..%d where dim P_n differs from A(n,1) under some convention:" % N, some)
    print("n in 1..%d where dim P_n differs from A(n,1) under every convention:" % N, both)
    ok &= both == list(range(3, N + 1))
    first = min(n for n in range(1, N + 1) if d1[n - 1] != A0[n - 1] and d1[n - 1] != A1[n - 1])
    print("smallest such n:", first, " dim P_%d = %d, A(%d,1) in {%d, %d}" % (
        first, d1[first - 1], first, A0[first - 1], A1[first - 1]))
    ok &= first == 3
    # robustness: 2 = dim P_3 is not A(m,1) for any m (values 2^m - m - 1 and 1)
    vals = {2 ** m - m - 1 for m in range(0, 64)} | {1}
    print("2 occurs among A(m,1), m < 64, any convention:", 2 in vals)
    ok &= 2 not in vals
    print("ALL CHECKS PASSED" if ok else "CHECK FAILED")
    if not ok:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
