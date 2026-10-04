#!/usr/bin/env python3
"""Independent check for conjecture 00000007608 (Python 3 standard library only).

Method (different from the Lean proof, which uses scaled integer matrices and normal forms):
genuine exact rational arithmetic (fractions.Fraction) on 2x2 / 3x3 matrices, mirrors computed
as kernels of A - I by Gaussian elimination, a tiny polynomial-arithmetic engine for the
symbolic identities, and brute-force enumeration of all decompositions inside a finite set of
rational reflections.

Checks
  1. 90 deg rotation: R2.R1 = R4.R3 with four pairwise different mirrors.
  2. 180 deg rotation: R3.R1 = R4.R2 = R2.R4 = -I.
  3. Symbolic: rho.A is a reflection for every rotation rho and reflection A; (rho.A).A = rho;
     the Pythagorean family A_t is a reflection with mirror spanned by (1, t).
  4. For many rational rotations rho != I: the decompositions (A_t, rho.A_t), t = 0..40 and
     rational t, are valid, non-parallel, with pairwise different mirrors.
  5. Brute force: in a set S of 124 rational reflections (Pythagorean triples), count all
     pairs (A, B) in S x S with B.A = rho; all non-parallel when rho != I; all parallel
     (equal mirrors) when rho = I.
  6. R^3 block embedding: plane mirrors, two decompositions of the 90 deg rotation about e3.
  7. Affine: parallel distinct mirrors give a fixed-point-free translation; the 90 deg rotation
     about (1, 1) has two decompositions with non-parallel mirrors.
  8. Real (irrational) angles, floating point illustration of R_beta R_alpha = rho_theta for
     every alpha with beta - alpha = theta/2.
"""
from fractions import Fraction as Fr
from math import gcd, cos, sin, isclose
import itertools
import sys

OK = True


def check(cond, msg):
    global OK
    print(("PASS " if cond else "FAIL ") + msg)
    if not cond:
        OK = False


# ------------------------------------------------------------------ matrices
def mat(rows):
    return tuple(tuple(Fr(x) for x in r) for r in rows)


def mul(A, B):
    n, k, m = len(A), len(B), len(B[0])
    return tuple(tuple(sum(A[i][t] * B[t][j] for t in range(k)) for j in range(m)) for i in range(n))


def tr(A):
    return tuple(zip(*A))


def eye(n):
    return tuple(tuple(Fr(int(i == j)) for j in range(n)) for i in range(n))


def det(A):
    n = len(A)
    if n == 1:
        return A[0][0]
    return sum((-1) ** j * A[0][j] * det(tuple(r[:j] + r[j + 1:] for r in A[1:])) for j in range(n))


def sub(A, B):
    return tuple(tuple(a - b for a, b in zip(r, s)) for r, s in zip(A, B))


def neg(A):
    return tuple(tuple(-a for a in r) for r in A)


def is_refl(A):
    n = len(A)
    return mul(A, tr(A)) == eye(n) and det(A) == -1 and mul(A, A) == eye(n)


def is_rot(A):
    n = len(A)
    return mul(A, tr(A)) == eye(n) and det(A) == 1


def kernel(M):
    """basis of the kernel of M (rational Gaussian elimination), as a canonical RREF tuple"""
    M = [list(r) for r in M]
    rows, cols = len(M), len(M[0])
    piv = []
    r = 0
    for c in range(cols):
        p = next((i for i in range(r, rows) if M[i][c] != 0), None)
        if p is None:
            continue
        M[r], M[p] = M[p], M[r]
        M[r] = [x / M[r][c] for x in M[r]]
        for i in range(rows):
            if i != r and M[i][c] != 0:
                M[i] = [a - M[i][c] * b for a, b in zip(M[i], M[r])]
        piv.append(c)
        r += 1
    free = [c for c in range(cols) if c not in piv]
    basis = []
    for f in free:
        v = [Fr(0)] * cols
        v[f] = Fr(1)
        for i, c in enumerate(piv):
            v[c] = -M[i][f]
        basis.append(tuple(v))
    return basis


def mirror(A):
    """the fixed subspace ker(A - I), canonically (RREF of the basis)"""
    B = kernel(sub(A, eye(len(A))))
    if not B:
        return ()
    # canonical form: RREF of the span
    M = [list(v) for v in B]
    rows, cols = len(M), len(M[0])
    r = 0
    for c in range(cols):
        p = next((i for i in range(r, rows) if M[i][c] != 0), None)
        if p is None:
            continue
        M[r], M[p] = M[p], M[r]
        M[r] = [x / M[r][c] for x in M[r]]
        for i in range(rows):
            if i != r and M[i][c] != 0:
                M[i] = [a - M[i][c] * b for a, b in zip(M[i], M[r])]
        r += 1
    return tuple(tuple(row) for row in M[:r])


R1 = mat([[1, 0], [0, -1]])
R2 = mat([[0, 1], [1, 0]])
R3 = mat([[-1, 0], [0, 1]])
R4 = mat([[0, -1], [-1, 0]])
ROT90 = mat([[0, -1], [1, 0]])
I2 = eye(2)


def rot(c, s):
    return mat([[c, -s], [s, c]])


def refl_t(t):
    t = Fr(t)
    q = 1 + t * t
    return mat([[(1 - t * t) / q, 2 * t / q], [2 * t / q, (t * t - 1) / q]])


# ------------------------------------------------------------------ 1, 2
print("== 1. the 90 degree rotation")
check(all(is_refl(R) for R in (R1, R2, R3, R4)), "R1..R4 are reflections (orthogonal, det -1, involution)")
check(is_rot(ROT90) and ROT90 != I2, "rot90 = [[0,-1],[1,0]] is a nontrivial rotation")
check(mul(R2, R1) == ROT90 and mul(R4, R3) == ROT90, "R2.R1 = R4.R3 = rot90")
ms = [mirror(R) for R in (R1, R2, R3, R4)]
check(all(len(m) == 1 for m in ms), "each mirror is a line: " + ", ".join(str([str(x) for x in m[0]]) for m in ms))
check(len(set(ms)) == 4, "the four mirrors (x-axis, y=x, y-axis, y=-x) are pairwise different lines")
check({ms[0], ms[1]} != {ms[2], ms[3]}, "the unordered mirror pairs {x-axis, y=x} and {y-axis, y=-x} differ")

print("== 2. the 180 degree rotation")
NEGI = neg(I2)
check(mul(R3, R1) == NEGI and mul(R4, R2) == NEGI and mul(R2, R4) == NEGI, "R3.R1 = R4.R2 = R2.R4 = -I")
check(mirror(R1) != mirror(R3) and mirror(R2) != mirror(R4) and {mirror(R1), mirror(R3)} != {mirror(R2), mirror(R4)},
      "non-parallel mirror pairs {x-axis, y-axis} and {y=x, y=-x} differ")

# ------------------------------------------------------------------ 3. symbolic
print("== 3. symbolic identities (polynomial arithmetic over Z)")


class P:
    """polynomial with integer coefficients: dict monomial(tuple of exponents) -> coeff"""
    VARS = ("x", "y", "a", "b", "t")

    def __init__(self, d=None):
        self.d = {k: v for k, v in (d or {}).items() if v != 0}

    @staticmethod
    def var(name):
        e = [0] * len(P.VARS)
        e[P.VARS.index(name)] = 1
        return P({tuple(e): 1})

    @staticmethod
    def const(c):
        return P({(0,) * len(P.VARS): c})

    def __add__(self, o):
        o = o if isinstance(o, P) else P.const(o)
        d = dict(self.d)
        for k, v in o.d.items():
            d[k] = d.get(k, 0) + v
        return P(d)

    __radd__ = __add__

    def __neg__(self):
        return P({k: -v for k, v in self.d.items()})

    def __sub__(self, o):
        return self + (-(o if isinstance(o, P) else P.const(o)))

    def __rsub__(self, o):
        return P.const(o) - self

    def __mul__(self, o):
        o = o if isinstance(o, P) else P.const(o)
        d = {}
        for k1, v1 in self.d.items():
            for k2, v2 in o.d.items():
                k = tuple(i + j for i, j in zip(k1, k2))
                d[k] = d.get(k, 0) + v1 * v2
        return P(d)

    __rmul__ = __mul__

    def __eq__(self, o):
        o = o if isinstance(o, P) else P.const(o)
        return self.d == o.d

    def __hash__(self):
        return hash(frozenset(self.d.items()))


x, y, a, b, t = (P.var(v) for v in P.VARS)


def pmul(A, B):
    return [[A[i][0] * B[0][j] + A[i][1] * B[1][j] for j in range(2)] for i in range(2)]


Rho = [[x, -y], [y, x]]          # rotation (times p), x^2 + y^2 = p^2
A = [[a, b], [b, -a]]            # reflection (times q), a^2 + b^2 = q^2
C = pmul(Rho, A)
check(C[1][0] == C[0][1] and C[1][1] == -C[0][0], "rho.A has the reflection shape [[a',b'],[b',-a']]")
check(C[0][0] * C[0][0] + C[0][1] * C[0][1] == (x * x + y * y) * (a * a + b * b),
      "a'^2 + b'^2 = (x^2+y^2)(a^2+b^2) = (pq)^2, so rho.A is orthogonal with det -1 (and an involution)")
CA = pmul(C, A)
check(all(CA[i][j] == Rho[i][j] * (a * a + b * b) for i in range(2) for j in range(2)),
      "(rho.A).A = (a^2+b^2) rho = q^2 rho, i.e. (rho.A).A = rho")
check(pmul(A, A) == [[a * a + b * b, P.const(0)], [P.const(0), a * a + b * b]],
      "A.A = (a^2+b^2) I: orthogonal + det -1 already forces the involution")
check((1 - t * t) * (1 - t * t) + (2 * t) * (2 * t) == (1 + t * t) * (1 + t * t),
      "(1-t^2)^2 + (2t)^2 = (1+t^2)^2 (Pythagorean family)")
At = [[1 - t * t, 2 * t], [2 * t, t * t - 1]]
fix = [At[0][0] * 1 + At[0][1] * t, At[1][0] * 1 + At[1][1] * t]
check(fix[0] == (1 + t * t) * 1 and fix[1] == (1 + t * t) * t, "A_t (1,t) = (1,t): the mirror of A_t is the line of slope t")

# ------------------------------------------------------------------ 4. many rotations
print("== 4. the family (A_t, rho.A_t) for many rational rotations")


def pyth(limit):
    res = set()
    for m in range(1, limit):
        for n in range(0, m):
            aa, bb, cc = m * m - n * n, 2 * m * n, m * m + n * n
            g = gcd(gcd(aa, bb), cc)
            aa, bb, cc = aa // g, bb // g, cc // g
            for sa, sb in itertools.product((1, -1), repeat=2):
                res.add((Fr(sa * aa, cc), Fr(sb * bb, cc)))
                res.add((Fr(sb * bb, cc), Fr(sa * aa, cc)))
    return sorted(res)


circle = pyth(9)
rotations = [rot(c, s) for c, s in circle if (c, s) != (1, 0)]
ts = [Fr(k) for k in range(0, 41)] + [Fr(p, q) for p in range(-7, 8) for q in range(1, 6) if gcd(p, q) == 1]
ts = sorted(set(ts))
good = True
for rho in rotations:
    assert is_rot(rho) and rho != I2
    seen = set()
    for tt in ts:
        At_ = refl_t(tt)
        Bt = mul(rho, At_)
        if not (is_refl(At_) and is_refl(Bt) and mul(Bt, At_) == rho and mirror(At_) != mirror(Bt)):
            good = False
        seen.add(mirror(At_))
    if len(seen) != len(ts):
        good = False
check(good, f"{len(rotations)} nontrivial rational rotations x {len(ts)} parameters t: every (A_t, rho.A_t) is a "
      "decomposition rho = B.A with non-parallel mirrors, and the mirrors of the A_t are pairwise different")

# ------------------------------------------------------------------ 5. brute force
print("== 5. brute force: all decompositions inside a finite set of rational reflections")
S = [mat([[c, s], [s, -c]]) for c, s in pyth(9)]
S = sorted(set(S))
maxden = max(R[0][0].denominator for R in S)
check(all(is_refl(R) for R in S), f"S = {len(S)} rational reflections [[c,s],[s,-c]] (c^2+s^2=1, from Pythagorean "
      f"triples (m^2-n^2, 2mn, m^2+n^2), 0 <= n < m < 9; largest denominator {maxden})")
for name, rho in (("rot90", ROT90), ("rot180", NEGI), ("rot(3/5,4/5)", rot(Fr(3, 5), Fr(4, 5))),
                  ("rot(5/13,12/13)", rot(Fr(5, 13), Fr(12, 13)))):
    dec = [(A_, B_) for A_ in S for B_ in S if mul(B_, A_) == rho]
    nonpar = all(mirror(A_) != mirror(B_) for A_, B_ in dec)
    unord = {frozenset((mirror(A_), mirror(B_))) for A_, B_ in dec}
    check(len(dec) > 2 and nonpar,
          f"{name}: {len(dec)} decompositions B.A = rho with A, B in S, all non-parallel, "
          f"{len(unord)} different unordered mirror pairs")
dec_id = [(A_, B_) for A_ in S for B_ in S if mul(B_, A_) == I2]
check(len(dec_id) == len(S) and all(A_ == B_ for A_, B_ in dec_id),
      f"identity: the {len(dec_id)} decompositions in S are exactly (A, A): equal mirrors (the 'parallel' exception)")
cls_ok = all(sum(1 for B_ in S if mul(B_, A_) == rho) <= 1 for rho in (ROT90, NEGI) for A_ in S)
check(cls_ok, "classification: for each first reflection A the second one is forced (B = rho.A)")

# ------------------------------------------------------------------ 6. R^3
print("== 6. R^3: hyperplane reflections (block embedding diag(R, 1))")


def blk(R):
    return mat([[R[0][0], R[0][1], 0], [R[1][0], R[1][1], 0], [0, 0, 1]])


E = [blk(R) for R in (R1, R2, R3, R4)]
ROTZ = blk(ROT90)
check(all(is_refl(M) for M in E) and is_rot(ROTZ), "diag(Ri,1) are reflections of R^3, diag(rot90,1) is a rotation")
check(mul(E[1], E[0]) == ROTZ and mul(E[3], E[2]) == ROTZ, "diag(R2,1).diag(R1,1) = diag(R4,1).diag(R3,1) = 90 deg about e3")
mp = [mirror(M) for M in E]
check(all(len(m) == 2 for m in mp) and len(set(mp)) == 4, "the four mirrors are planes (dim 2), pairwise different")
# a genuinely 3D family: reflections in planes containing the axis e3 with normal (n1, n2, 0)
fam3 = [blk(refl_t(k)) for k in range(0, 20)]
check(all(mul(mul(ROTZ, M), M) == ROTZ and is_refl(mul(ROTZ, M)) for M in fam3)
      and len({mirror(M) for M in fam3}) == 20, "R^3: 20 decompositions (M, rotz.M) with different mirror planes")

# ------------------------------------------------------------------ 7. affine
print("== 7. affine reflections")


def aff(M, u):
    return (M, (Fr(u[0]), Fr(u[1])))


def acomp(G, F):
    M = mul(G[0], F[0])
    v = (G[0][0][0] * F[1][0] + G[0][0][1] * F[1][1] + G[1][0], G[0][1][0] * F[1][0] + G[0][1][1] * F[1][1] + G[1][1])
    return (M, v)


def aapp(F, v):
    return (F[0][0][0] * v[0] + F[0][0][1] * v[1] + F[1][0], F[0][1][0] * v[0] + F[0][1][1] * v[1] + F[1][1])


def afixed(F):
    """fixed points of v -> Mv + u: solve (M - I) v = -u; returns 'none', 'point' or 'line'/'plane'"""
    M = sub(F[0], I2)
    aug = [list(M[i]) + [-F[1][i]] for i in range(2)]
    # rank computations
    def rank(rows):
        rows = [list(r) for r in rows]
        r = 0
        for c in range(len(rows[0])):
            p = next((i for i in range(r, len(rows)) if rows[i][c] != 0), None)
            if p is None:
                continue
            rows[r], rows[p] = rows[p], rows[r]
            for i in range(len(rows)):
                if i != r and rows[i][c] != 0:
                    f = rows[i][c] / rows[r][c]
                    rows[i] = [x_ - f * y_ for x_, y_ in zip(rows[i], rows[r])]
            r += 1
        return r
    rM, rA = rank(M), rank(aug)
    if rA > rM:
        return "none"
    return {2: "point", 1: "line", 0: "plane"}[rM]


ID = aff(I2, (0, 0))
Sx0, Sx1 = aff(R3, (0, 0)), aff(R3, (2, 0))
T = acomp(Sx1, Sx0)
check(acomp(Sx0, Sx0) == ID and acomp(Sx1, Sx1) == ID and afixed(Sx0) == "line" and afixed(Sx1) == "line",
      "reflections in x = 0 and x = 1: involutions whose fixed sets are lines")
check(aapp(Sx0, (0, 0)) == (0, 0) and aapp(Sx1, (0, 0)) != (0, 0) and Sx0[0] == Sx1[0],
      "the mirrors x = 0, x = 1 are parallel and distinct")
check(T == aff(I2, (2, 0)) and afixed(T) == "none",
      "their composition is the translation by (2, 0): no fixed point, so not a rotation (clause 1 fails, clause 4's exception)")
check(acomp(Sx0, Sx0) == ID, "equal mirrors: S.S = id")
RotC = aff(ROT90, (2, 0))
Sy1, Sdiag, Santi = aff(R1, (0, 2)), aff(R2, (0, 0)), aff(R4, (2, 2))
check(afixed(RotC) == "point" and aapp(RotC, (1, 1)) == (1, 1), "RotC = rotation by 90 deg about (1, 1)")
check(all(acomp(F, F) == ID for F in (Sy1, Sdiag, Sx1, Santi)), "Sy1, Sdiag, Sx1, Santi are affine reflections")
check(acomp(Sdiag, Sy1) == RotC and acomp(Santi, Sx1) == RotC,
      "RotC = S(y=x) o S(y=1) = S(x+y=2) o S(x=1): two decompositions, four non-parallel mirrors through (1,1)")

# ------------------------------------------------------------------ 8. real angles
print("== 8. real angles (floating point illustration)")


def R_line(al):
    return ((cos(2 * al), sin(2 * al)), (sin(2 * al), -cos(2 * al)))


def rotf(th):
    return ((cos(th), -sin(th)), (sin(th), cos(th)))


def fmul(A_, B_):
    return [[sum(A_[i][k] * B_[k][j] for k in range(2)) for j in range(2)] for i in range(2)]


fl = True
for th in (1.0, 0.3, 2.5, 3.14159, -1.7):
    for al in (0.0, 0.1, 0.77, 1.3, 2.9):
        P_ = fmul(R_line(al + th / 2), R_line(al))
        Q_ = rotf(th)
        fl &= all(isclose(P_[i][j], Q_[i][j], abs_tol=1e-12) for i in range(2) for j in range(2))
check(fl, "R_(alpha + theta/2) . R_alpha = rho_theta for 5 angles theta and 5 angles alpha each")

print()
print("ALL CHECKS PASSED" if OK else "SOME CHECK FAILED")
sys.exit(0 if OK else 1)
