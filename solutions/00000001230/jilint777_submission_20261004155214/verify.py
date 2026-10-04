#!/usr/bin/env python3
"""Independent check for the disproof of conjecture 00000001230 (Python 3 standard library only).

Method (different from the Lean proof, which uses explicit witnesses and a
"4x = 0 => 2x = 0" invariant): build grid graphs from coordinates, compute the
Smith normal form of the (reduced and full) Laplacian with exact integer
arithmetic, read off the invariant factors of the sandpile group, and compare
with every group of the form  (+)_S (Z/gcd S)^{e(S)}.

Criterion. Let D be the multiset of moduli gcd(S). A group (+)_d (Z/d)^{e_d}
(d in D) is finite iff e_0 = 0, and then its exponent divides
lcm{d in D : d > 0}. The sandpile group is finite, so an isomorphism forces
the largest invariant factor of Jac to divide that lcm. When it does not,
no choice of exponents (finite or infinite) works.
"""
from fractions import Fraction
from itertools import product
from math import gcd

FAIL = []


def check(cond, msg):
    print(("ok   " if cond else "FAIL ") + msg)
    if not cond:
        FAIL.append(msg)


def lcm(a, b):
    return a * b // gcd(a, b)


# ---------------------------------------------------------------- graphs
def grid(ms):
    V = list(product(*[range(m) for m in ms]))
    adj = lambda u, v: sum(abs(a - b) for a, b in zip(u, v)) == 1
    L = [[(sum(adj(u, w) for w in V) if u == v else (-1 if adj(u, v) else 0)) for v in V] for u in V]
    return V, L


def torus(ms):
    V = list(product(*[range(m) for m in ms]))
    idx = {v: i for i, v in enumerate(V)}
    n = len(V)
    L = [[0] * n for _ in range(n)]
    for v in V:
        for k, m in enumerate(ms):
            w = list(v); w[k] = (w[k] + 1) % m; w = tuple(w)
            a, b = idx[v], idx[w]
            L[a][a] += 1; L[b][b] += 1; L[a][b] -= 1; L[b][a] -= 1
    return V, L


def reduced(L):
    return [r[1:] for r in L[1:]]


# ---------------------------------------------------------------- Smith normal form
def smith(M):
    """Invariant factors d1 | d2 | ... (zeros for the free part) of an integer matrix."""
    A = [row[:] for row in M]
    n, m = len(A), len(A[0])
    diag = []
    t = 0
    while t < min(n, m):
        nz = [(abs(A[i][j]), i, j) for i in range(t, n) for j in range(t, m) if A[i][j] != 0]
        if not nz:
            break
        _, i, j = min(nz)
        A[t], A[i] = A[i], A[t]
        for row in A:
            row[t], row[j] = row[j], row[t]
        changed = True
        while changed:
            changed = False
            p = A[t][t]
            for i in range(t + 1, n):
                q = A[i][t] // p
                if q:
                    A[i] = [a - q * b for a, b in zip(A[i], A[t])]
                if A[i][t] != 0:
                    A[t], A[i] = A[i], A[t]; changed = True; break
            if changed:
                continue
            p = A[t][t]
            for j in range(t + 1, m):
                q = A[t][j] // p
                if q:
                    for row in A:
                        row[j] -= q * row[t]
                if A[t][j] != 0:
                    for row in A:
                        row[t], row[j] = row[j], row[t]
                    changed = True; break
            if changed:
                continue
            # divisibility condition
            p = A[t][t]
            for i in range(t + 1, n):
                if any(A[i][j] % p for j in range(t + 1, m)):
                    A[t] = [a + b for a, b in zip(A[t], A[i])]
                    changed = True; break
        diag.append(abs(A[t][t]))
        t += 1
    diag += [0] * (min(n, m) - len(diag))
    # normalise to divisibility chain (diagonal SNF is unique up to this)
    for a in range(len(diag)):
        for b in range(a + 1, len(diag)):
            x, y = diag[a], diag[b]
            g = gcd(x, y); l = lcm(x, y) if x and y else 0
            diag[a], diag[b] = g, l
    return diag


def det(M):
    A = [[Fraction(x) for x in r] for r in M]
    n = len(A); d = Fraction(1)
    for c in range(n):
        p = next((i for i in range(c, n) if A[i][c] != 0), None)
        if p is None:
            return 0
        if p != c:
            A[c], A[p] = A[p], A[c]; d = -d
        d *= A[c][c]
        for i in range(c + 1, n):
            f = A[i][c] / A[c][c]
            A[i] = [x - f * y for x, y in zip(A[i], A[c])]
    return int(d)


def solve(M, b):
    n = len(M)
    A = [[Fraction(x) for x in r] + [Fraction(y)] for r, y in zip(M, b)]
    for c in range(n):
        p = next(i for i in range(c, n) if A[i][c] != 0)
        A[c], A[p] = A[p], A[c]
        for i in range(n):
            if i != c and A[i][c] != 0:
                f = A[i][c] / A[c][c]
                A[i] = [x - f * y for x, y in zip(A[i], A[c])]
    return [A[i][n] / A[i][i] for i in range(n)]


def matvec(M, z):
    return [sum(a * b for a, b in zip(r, z)) for r in M]


# ---------------------------------------------------------------- conjectured moduli
def moduli(ms):
    """gcd(S) over all 2^n index subsets S (gcd of the empty set = 0)."""
    out = []
    for mask in range(1 << len(ms)):
        g = 0
        for k, m in enumerate(ms):
            if mask >> k & 1:
                g = gcd(g, m)
        out.append(g)
    return out


def representable(inv, mods):
    """Can a finite group with invariant factors inv be (+)_d (Z/d)^{e_d}, d in mods?"""
    nonzero = [d for d in mods if d > 0]
    if not nonzero:
        return all(x == 1 for x in inv)  # only the trivial finite group
    L = 1
    for d in nonzero:
        L = lcm(L, d)
    return all(L % x == 0 for x in inv)


def jac(ms):
    V, L = grid(ms)
    inv = [d for d in smith(reduced(L)) if d != 1]
    return V, L, inv


# ---------------------------------------------------------------- main checks
print("== the 2x2 grid is the 4-cycle")
V, L, inv = jac([2, 2])
check(V == [(0, 0), (0, 1), (1, 0), (1, 1)], "vertices of [2]x[2]: %s" % V)
check(reduced(L) == [[2, 0, -1], [0, 2, -1], [-1, -1, 2]], "reduced Laplacian = %s" % reduced(L))
check(all(sum(r[k] for r in L) == 0 for k in range(4)) and all(L[i][i] == 2 for i in range(4)),
      "full Laplacian is 2-regular with zero column sums (the cycle C4)")
check(det(reduced(L)) == 4, "det of reduced Laplacian = number of spanning trees = 4")
check(inv == [4], "Jac([2]x[2]) invariant factors %s, i.e. Z/4" % inv)
full = smith(L)
check(sorted(full) == [0, 1, 1, 4], "full Laplacian SNF %s: Z^V/im L = Z + Z/4" % full)

print("== explicit witnesses used in Lean")
R = reduced(L)
check(matvec(R, [3, 1, 2]) == [4, 0, 0], "Ltilde (3,1,2) = 4 e0")
sol = solve(R, [2, 0, 0])
check(any(x.denominator != 1 for x in sol), "Ltilde z = 2 e0 has only the non-integral solution %s" % [str(x) for x in sol])
check(matvec(L, [0, 3, 1, 2]) == [-4, 4, 0, 0], "L (0,3,1,2) = 4((0,1)-(0,0))")
check(all(sum(r) == 0 for r in zip(*L)), "every column of L sums to 0, so degree is well defined")
# L z = 2((0,1)-(0,0)): adding a constant to z does not change L z (rows sum to 0), so we may
# take z(0,0) = 0; rows (0,1),(1,0),(1,1) then read Ltilde z' = (2,0,0)
zs = solve(R, [2, 0, 0])
check(any(x.denominator != 1 for x in zs), "L z = 2((0,1)-(0,0)) has no integer solution (reduces to the sink-normalised system)")
VQ, LQ, invQ = jac([2, 2, 2])
RQ = reduced(LQ)
check(matvec(RQ, [3, 3, 6, 2, 3, 3, 4]) == [0, 0, 8, 0, 0, 0, 0], "cube: Ltilde (3,3,6,2,3,3,4) = 8 e2 (vertex (0,1,1))")
solq = solve(RQ, [0, 0, 4, 0, 0, 0, 0])
check(any(x.denominator != 1 for x in solq), "cube: Ltilde z = 4 e2 has no integer solution")
check(invQ == [2, 8, 24], "Jac([2]^3) invariant factors %s" % invQ)

print("== phi(x) = 3x0 + x1 + 2x2 mod 4 kills the columns of Ltilde (Lean's iso Jac(C4) = Z/4)")
check(all((3 * c[0] + c[1] + 2 * c[2]) % 4 == 0 for c in zip(*R)), "columns annihilated mod 4")

print("== comparison with (+)_S (Z/gcd S)^{e(S)} for every exponent choice")
cases = [([2, 2], "vertex"), ([2, 3], "vertex"), ([3, 3], "vertex"), ([2, 2, 2], "vertex"),
         ([2, 4], "vertex"), ([3, 4], "vertex")]
for ms, conv in cases:
    _, _, inv = jac(ms)
    mv = sorted(set(moduli(ms)))
    me = sorted(set(moduli([m - 1 for m in ms])))
    rv = representable(inv, mv)
    re_ = representable(inv, me)
    check(not rv and not re_,
          "grid %s: Jac invariants %s; vertex-convention moduli %s -> representable %s; "
          "edge-convention moduli %s -> representable %s" % ("x".join(map(str, ms)), inv, mv, rv, me, re_))

print("== the gcd(empty set) convention does not matter")
for g0 in (0, 1):
    mods = [g0] + moduli([2, 2])[1:]
    check(not representable([4], mods), "gcd(empty)=%d: moduli %s, Z/4 not representable" % (g0, sorted(set(mods))))

print("== sanity: the predicate is satisfiable (trees, n = 1)")
for m in range(2, 8):
    _, _, inv = jac([m])
    check(inv == [] and representable(inv, moduli([m])), "path [%d]: Jac trivial, representable with e = 0" % m)

print("== remark: torus reading (not the stated object) also fails")
for ms in ([3, 3], [3, 4]):
    V, L = torus(ms)
    inv = [d for d in smith(reduced(L)) if d != 1]
    check(not representable(inv, sorted(set(moduli(ms)))),
          "torus C%d x C%d: Jac invariants %s, moduli %s" % (ms[0], ms[1], inv, sorted(set(moduli(ms)))))

print()
if FAIL:
    print("FAILED: %d checks" % len(FAIL))
    raise SystemExit(1)
print("ALL CHECKS PASSED")
