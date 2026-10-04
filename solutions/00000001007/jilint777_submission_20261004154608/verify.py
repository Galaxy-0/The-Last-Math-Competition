#!/usr/bin/env python3
"""Independent check (Python 3 standard library only) of the disproof of
conjecture 00000001007: the Suzuki-Tits ovoid of Q(4,8) is not an elliptic quadric.

GF(8) is built here from discrete logarithms (powers of a primitive element),
not from the multiplication table used in Lean.  All checks are exhaustive:
  * GF(8) is a field of characteristic 2;
  * the Tits set T is an ovoid of PG(3,8) (65 points, no three collinear);
  * its lift to Q(4,8): x0x3 + x1x2 + x4^2 = 0 is an ovoid of Q(4,8) in the
    defining sense: every one of the 585 lines of Q(4,8) meets it in exactly
    one point (and it consists of 65 pairwise non-collinear points);
  * no hyperplane of PG(4,8) contains it (all 4681 hyperplanes tried);
  * its projection to PG(3,8) lies on no quadric (rank of the 65x10 monomial
    matrix is 10);
  * control: the elliptic quadric Q(4,8) n {x4 = x1 + x2} is an ovoid, equals a
    hyperplane section, and lies on a quadric of PG(3,8).
"""
import itertools, sys

# ---------- GF(8) via logarithms: w^3 = w + 1, elements = 3-bit vectors ----------
EXP = [1]
for _ in range(6):
    v = EXP[-1] << 1
    if v & 8:
        v ^= 0b1011
    EXP.append(v)
assert sorted(EXP) == list(range(1, 8)), "w is primitive"
LOG = {v: i for i, v in enumerate(EXP)}
F = range(8)
def mul(a, b):
    if a == 0 or b == 0:
        return 0
    return EXP[(LOG[a] + LOG[b]) % 7]
def inv(a):
    return EXP[(-LOG[a]) % 7]
def pw(a, e):
    r = 1
    for _ in range(e):
        r = mul(r, a)
    return r

ok = True
def check(name, cond):
    global ok
    print(("PASS " if cond else "FAIL ") + name)
    ok = ok and cond

check("GF(8): associative, commutative, distributive, inverses, char 2",
      all(mul(mul(a, b), c) == mul(a, mul(b, c)) and mul(a, b ^ c) == mul(a, b) ^ mul(a, c)
          for a in F for b in F for c in F)
      and all(mul(a, b) == mul(b, a) for a in F for b in F)
      and all(mul(a, inv(a)) == 1 for a in F if a) and all(a ^ a == 0 for a in F))
sigma = lambda x: pw(x, 4)
check("sigma(x)=x^4 is an automorphism with sigma^2 = Frobenius x->x^2",
      all(sigma(a ^ b) == sigma(a) ^ sigma(b) and sigma(mul(a, b)) == mul(sigma(a), sigma(b))
          for a in F for b in F) and all(sigma(sigma(x)) == mul(x, x) for x in F))

def normalize(v):
    i = next(k for k in range(len(v)) if v[k])
    c = inv(v[i])
    return tuple(mul(c, t) for t in v)

def rank(rows):
    rows = [list(r) for r in rows]
    rk = 0
    for c in range(len(rows[0])):
        p = next((i for i in range(rk, len(rows)) if rows[i][c]), None)
        if p is None:
            continue
        rows[rk], rows[p] = rows[p], rows[rk]
        iv = inv(rows[rk][c])
        rows[rk] = [mul(iv, t) for t in rows[rk]]
        for i in range(len(rows)):
            if i != rk and rows[i][c]:
                f = rows[i][c]
                rows[i] = [a ^ mul(f, b) for a, b in zip(rows[i], rows[rk])]
        rk += 1
    return rk

# ---------- the Tits ovoid of PG(3,8) ----------
T3 = [(1, x, y, mul(x, y) ^ mul(sigma(x), mul(x, x)) ^ sigma(y)) for x in F for y in F] + [(0, 0, 0, 1)]
check("Tits set: 65 distinct points of PG(3,8)", len({normalize(p) for p in T3}) == 65)
check("Tits set: no three collinear (all 43680 triples have rank 3) => ovoid of PG(3,8)",
      all(rank(t) == 3 for t in itertools.combinations(T3, 3)))

# ---------- Q(4,8) ----------
def Q(v):
    return mul(v[0], v[3]) ^ mul(v[1], v[2]) ^ mul(v[4], v[4])
def pol(u, v):
    return mul(u[0], v[3]) ^ mul(u[3], v[0]) ^ mul(u[1], v[2]) ^ mul(u[2], v[1])
# Q(u+v) - Q(u) - Q(v) = pol(u,v) holds coordinatewise because, for all a,b,c,d:
#   (a+b)(c+d) = ac + bd + (ad + bc)   and   (a+b)^2 = a^2 + b^2   (char 2).
check("polar form: the two identities giving Q(u+v) = Q(u) + Q(v) + pol(u,v) (exhaustive)",
      all(mul(a ^ b, c ^ d) == mul(a, c) ^ mul(b, d) ^ mul(a, d) ^ mul(b, c)
          for a in F for b in F for c in F for d in F)
      and all(mul(a ^ b, a ^ b) == mul(a, a) ^ mul(b, b) for a in F for b in F))
check("Q nondegenerate: radical of pol is <(0,0,0,0,1)> and Q(0,0,0,0,1) = 1",
      [v for v in itertools.product(F, repeat=5)
       if any(v) and all(pol(v, e) == 0 for e in [(1,0,0,0,0),(0,1,0,0,0),(0,0,1,0,0),(0,0,0,1,0),(0,0,0,0,1)])]
      == [(0, 0, 0, 0, t) for t in range(1, 8)] and Q((0, 0, 0, 0, 1)) == 1)

PTS = sorted({normalize(v) for v in itertools.product(F, repeat=5) if any(v)})
QP = [p for p in PTS if Q(p) == 0]
check("PG(4,8) has 4681 points, Q(4,8) has 585 = (q^4-1)/(q-1) points", len(PTS) == 4681 and len(QP) == 585)

LINES = set()
for x in QP:
    for y in QP:
        if x < y and pol(x, y) == 0:
            L = frozenset([x] + [normalize(tuple(a ^ mul(t, b) for a, b in zip(y, x))) for t in F])
            LINES.add(L)
check("Q(4,8) has 585 lines, 9 points each, all on the quadric",
      len(LINES) == 585 and all(len(L) == 9 and all(Q(p) == 0 for p in L) for L in LINES))

def sqrt(a):
    return next(b for b in F if mul(b, b) == a)
TITS = [p + (sqrt(mul(p[0], p[3]) ^ mul(p[1], p[2])),) for p in T3]
check("lift x4 = sqrt(x0x3+x1x2) equals x^3 + y^2 (formula used in Lean)",
      all(TITS[8 * x + y][4] == pw(x, 3) ^ mul(y, y) for x in F for y in F) and TITS[64] == (0, 0, 0, 1, 0))

def is_ovoid(O):
    S = set(O)
    return (len(S) == 65 and all(normalize(p) == p and Q(p) == 0 for p in O)
            and all(len(L & S) == 1 for L in LINES))
def pairwise_noncollinear(O):
    return all(pol(u, v) != 0 for u, v in itertools.combinations(O, 2))
check("lifted Tits set is an ovoid of Q(4,8): every line meets it exactly once", is_ovoid(TITS))
check("lifted Tits set: 65 pairwise non-collinear points (pol != 0, 2080 pairs)", pairwise_noncollinear(TITS))

HYP = PTS  # normalized functionals a, hyperplane sum a_i x_i = 0
def in_some_hyperplane(O):
    return [a for a in HYP if all((mul(a[0], p[0]) ^ mul(a[1], p[1]) ^ mul(a[2], p[2]) ^ mul(a[3], p[3]) ^ mul(a[4], p[4])) == 0
                for p in O)]
check("Tits ovoid lies in none of the 4681 hyperplanes of PG(4,8)", in_some_hyperplane(TITS) == [])
check("rank of the lifted Tits ovoid in GF(8)^5 is 5", rank(TITS) == 5)
MON = lambda p: [mul(p[i], p[j]) for i in range(4) for j in range(i, 4)]
check("projection to PG(3,8) lies on no quadric: 65x10 monomial matrix has rank 10",
      rank([MON(p) for p in TITS]) == 10)

# ---------- control: the elliptic quadric ----------
ELL = [(1, a, b, mul(a, a) ^ mul(a, b) ^ mul(b, b), a ^ b) for a in F for b in F] + [(0, 0, 0, 1, 0)]
SEC = [p for p in QP if p[1] ^ p[2] ^ p[4] == 0]
check("control: Q(4,8) n {x4 = x1 + x2} is exactly the 65-point set ELL", sorted(SEC) == sorted(ELL))
check("control: ELL is an ovoid of Q(4,8) (line definition) with pairwise non-collinear points",
      is_ovoid(ELL) and pairwise_noncollinear(ELL))
check("control: ELL lies in exactly one hyperplane, and its projection lies on a quadric (rank 9)",
      in_some_hyperplane(ELL) == [(0, 1, 1, 0, 1)] and rank([MON(p) for p in ELL]) == 9)
check("Tits ovoid != ELL (they share only 5 points)", len(set(TITS) & set(ELL)) == 5)

print("ALL CHECKS PASSED" if ok else "SOME CHECK FAILED")
sys.exit(0 if ok else 1)
