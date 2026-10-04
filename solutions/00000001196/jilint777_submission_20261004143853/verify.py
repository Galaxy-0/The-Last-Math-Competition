#!/usr/bin/env python3
"""Independent check for conjecture 00000001196 (Python 3 standard library only).

Schur Q- and P-functions are computed here from the COMBINATORIAL definition
(marked shifted tableaux, Macdonald III (8.16)), not from the Pfaffian formula
used in Lean.  The Pfaffian definition is then checked against it.
Products Q_k*Q_k, P_k*P_k, P_k*Q_k are expanded in the Q- and P-bases by exact
Gaussian elimination over the rationals, and the maximal coefficient is
compared with the conjectured value 2^(k-1) and the bound 2^(l(k)) = 2.
"""
from fractions import Fraction as Fr
from collections import defaultdict
from itertools import product

def strict_partitions(n, maxpart=None):
    if maxpart is None:
        maxpart = n
    if n == 0:
        yield ()
        return
    for a in range(min(n, maxpart), 0, -1):
        for rest in strict_partitions(n - a, a - 1):
            yield (a,) + rest

def tableau_poly(shape, nvars, P=False):
    """Sum of x^T over marked shifted tableaux T of the given strict shape with
    entries in 1'<1<2'<2<...<n'<n.  Code: 2i-1 = i', 2i = i.
    Rows/columns weakly increasing; an unprimed letter at most once per column,
    a primed letter at most once per row.  P=True: diagonal entries unprimed."""
    cells = [(i, j) for i, r in enumerate(shape) for j in range(i, i + r)]
    poly = defaultdict(int)
    T = {}
    def rec(idx):
        if idx == len(cells):
            e = [0] * nvars
            for v in T.values():
                e[(v + 1) // 2 - 1] += 1
            poly[tuple(e)] += 1
            return
        i, j = cells[idx]
        lo = 1
        left, up = T.get((i, j - 1)), T.get((i - 1, j))
        for v in range(1, 2 * nvars + 1):
            if left is not None and (v < left or (v == left and v % 2 == 1)):
                continue
            if up is not None and (v < up or (v == up and v % 2 == 0)):
                continue
            if P and i == j and v % 2 == 1:
                continue
            T[(i, j)] = v
            rec(idx + 1)
            del T[(i, j)]
    rec(0)
    return {m: c for m, c in poly.items() if c}

def pmul(a, b):
    r = defaultdict(int)
    for m1, c1 in a.items():
        for m2, c2 in b.items():
            r[tuple(x + y for x, y in zip(m1, m2))] += c1 * c2
    return {m: c for m, c in r.items() if c}

def padd(a, b, s=1):
    r = defaultdict(int)
    for m, c in a.items():
        r[m] += c
    for m, c in b.items():
        r[m] += s * c
    return {m: c for m, c in r.items() if c}

def pscale(a, s):
    return {m: c * s for m, c in a.items() if c * s}

def solve(target, basis):
    """Unique rational solution c of target = sum c_i basis_i, or raise."""
    mons = sorted(set(m for v in basis + [target] for m in v))
    nb = len(basis)
    rows = [[Fr(v.get(m, 0)) for v in basis] + [Fr(target.get(m, 0))] for m in mons]
    r = 0
    piv = []
    for c in range(nb):
        p = next((i for i in range(r, len(rows)) if rows[i][c] != 0), None)
        assert p is not None, "basis not linearly independent"
        rows[r], rows[p] = rows[p], rows[r]
        pv = rows[r][c]
        rows[r] = [x / pv for x in rows[r]]
        for i in range(len(rows)):
            if i != r and rows[i][c] != 0:
                f = rows[i][c]
                rows[i] = [x - f * y for x, y in zip(rows[i], rows[r])]
        piv.append(c)
        r += 1
    assert all(x == 0 for row in rows[r:] for x in row), "no expansion"
    return [rows[i][nb] for i in range(nb)]

# ---- 1. the Pfaffian definition used in Lean agrees with tableaux (n = 3, degree 6) ----
N3 = 3
def q_gen(r, n):
    """coefficient of t^r in prod_i (1+x_i t)/(1-x_i t) = prod_i (1 + 2 sum_{s>=1} x_i^s t^s)."""
    out = {}
    for e in product(range(r + 1), repeat=n):
        if sum(e) == r:
            c = 1
            for s in e:
                c *= 1 if s == 0 else 2
            out[e] = c
    return out
def Q2(a, b, n):
    res = pmul(q_gen(a, n), q_gen(b, n))
    for i in range(1, b + 1):
        res = padd(res, pmul(q_gen(a + i, n), q_gen(b - i, n)), 2 * (-1) ** i)
    return res
def Qpf(nu, n):
    if len(nu) == 1:
        return q_gen(nu[0], n)
    if len(nu) == 2:
        return Q2(nu[0], nu[1], n)
    a, b, c = nu
    t = pmul(Q2(a, b, n), q_gen(c, n))
    t = padd(t, pmul(Q2(a, c, n), q_gen(b, n)), -1)
    t = padd(t, pmul(q_gen(a, n), Q2(b, c, n)))
    return t
def e_poly(a, n):
    out = {}
    for e in product(range(2), repeat=n):
        if sum(e) == a:
            out[e] = 1
    return out
def h_poly(b, n):
    return {e: 1 for e in product(range(b + 1), repeat=n) if sum(e) == b}
for r in range(0, 9):
    s = {}
    for a in range(r + 1):
        s = padd(s, pmul(e_poly(a, N3), h_poly(r - a, N3)))
    assert s == q_gen(r, N3) == tableau_poly((r,), N3) if r > 0 else s == q_gen(0, N3)
print("q_r = sum_{a+b=r} e_a h_b = Q_(r) (tableaux), r = 0..8, 3 variables: OK")
for r in range(1, 9):
    s = {}
    for i in range(r + 1):
        s = padd(s, pmul(q_gen(i, N3), q_gen(r - i, N3)), (-1) ** i)
    assert s == {}
print("relation sum_i (-1)^i q_i q_(r-i) = 0, r = 1..8: OK")
for nu in strict_partitions(6):
    assert Qpf(nu, N3) == tableau_poly(nu, N3), nu
    Pt = tableau_poly(nu, N3, P=True)
    assert pscale(Pt, 2 ** len(nu)) == tableau_poly(nu, N3), nu
print("Pfaffian definition of Q_nu = marked-shifted-tableaux definition, all strict nu |- 6, 3 variables: OK")
print("Q_nu = 2^l(nu) P_nu (tableaux), all strict nu |- 6: OK")

# ---- 2. expansions for k = 1..5, all six normalisation readings ----
readings = [("P*P", "P"), ("Q*Q", "Q"), ("P*Q", "P"), ("P*Q", "Q"), ("Q*Q", "P"), ("P*P", "Q")]
print()
print("k  claim2^(k-1) | max coefficient under readings " + ", ".join(f"{p} in {b}" for p, b in readings))
results = {}
for k in range(1, 6):
    n = max(1, max(len(nu) for nu in strict_partitions(2 * k)))  # enough variables
    nus = list(strict_partitions(2 * k))
    Qb = [tableau_poly(nu, n) for nu in nus]
    Pb = [tableau_poly(nu, n, P=True) for nu in nus]
    Qk, Pk = tableau_poly((k,), n), tableau_poly((k,), n, P=True)
    prods = {"P*P": pmul(Pk, Pk), "Q*Q": pmul(Qk, Qk), "P*Q": pmul(Pk, Qk)}
    assert pmul(Pk, Qk) == pmul(Qk, Pk)
    row = []
    for pr, b in readings:
        c = solve(prods[pr], Pb if b == "P" else Qb)
        exp = {nu: cc for nu, cc in zip(nus, c) if cc}
        results[(k, pr, b)] = exp
        row.append(max(exp.values()))
    print(f"{k}  {2**(k-1):>5}        | " + "  ".join(str(x) for x in row))
print()
for k in (3, 4):
    for pr, b in readings:
        exp = results[(k, pr, b)]
        print(f"k={k}: {pr} = " + " + ".join(f"{c}*{b}{''.join(map(str, nu))}" for nu, c in exp.items()))
    print()

# ---- 3. the decisive case k = 3 ----
k = 3
ok_value_std = all(max(results[(3, pr, b)].values()) != 4 for pr, b in [("P*P", "P"), ("Q*Q", "Q")])
# general k: Q_k Q_k = 2 * sum_{j=0}^{k-1} Q_(2k-j, j)  (proved by hand in the report)
for k in range(1, 6):
    exp = results[(k, "Q*Q", "Q")]
    assert exp == {((2 * k - j, j) if j else (2 * k,)): 2 for j in range(k)}, k
    expP = results[(k, "P*P", "P")]
    assert expP == {((2 * k - j, j) if j else (2 * k,)): (2 if j else 1) for j in range(k)}, k
print("Q_k Q_k = 2 sum_j Q_(2k-j,j) and P_k P_k = P_(2k) + 2 sum_(j>=1) P_(2k-j,j), k = 1..5: OK")
print("smallest k with M((k),(k)) != 2^(k-1) in the standard readings (P*P in P, Q*Q in Q):",
      min(k for k in range(1, 6) if max(results[(k, "P*P", "P")].values()) != 2 ** (k - 1)
          and max(results[(k, "Q*Q", "Q")].values()) != 2 ** (k - 1)))
print()
print("k=3, standard readings (Stembridge P*P in P; Q*Q in Q): max coefficient = 2 != 4:", ok_value_std)
every = True
for pr, b in readings:
    M = max(results[(3, pr, b)].values())
    value_ok = (M == 4)
    bound_ok = (M <= 2)
    every = every and not (value_ok and bound_ok)
    print(f"  reading {pr} in {b}: M((3),(3)) = {M}; value clause M = 4: {value_ok}; bound clause M <= 2: {bound_ok}")
print("k=3: under every reading, the value clause or the bound clause fails:", every)
# linear independence in 3 variables (degree 6): rank 4 = number of strict partitions of 6
nus6 = list(strict_partitions(6))
mons = [(6, 0, 0), (5, 1, 0), (4, 2, 0), (3, 2, 1)]
Qb6 = [tableau_poly(nu, 3) for nu in nus6]
print("strict partitions of 6:", nus6)
print("coefficients of Q_nu at x^(6,0,0), x^(5,1,0), x^(4,2,0), x^(3,2,1):")
for nu, v in zip(nus6, Qb6):
    print("  Q" + "".join(map(str, nu)), [v.get(m, 0) for m in mons])
T = {"Q*Q": pmul(tableau_poly((3,), 3), tableau_poly((3,), 3)),
     "P*P": pmul(tableau_poly((3,), 3, P=True), tableau_poly((3,), 3, P=True)),
     "P*Q": pmul(tableau_poly((3,), 3, P=True), tableau_poly((3,), 3))}
for kk, v in T.items():
    print(f"coefficients of {kk[0]}3*{kk[2]}3 at the same monomials:", [v.get(m, 0) for m in mons])
assert every and ok_value_std
print("ALL CHECKS PASSED")
