#!/usr/bin/env python3
"""Independent check for the disproof of conjecture 00000007739 (Python 3 standard library only).

Claim (C1):  M_4(d)^2 = f(d) := 2 - (1 - 2^{-d})/d,  where M_p(d) = ||W||_p / ||W||_2 for free words
W of length d in a free semicircular family.

Exact rational arithmetic throughout (fractions.Fraction, Gaussian rationals for complex coefficients).
Two independent ways to compute the moments:
  (A) sparse operators on the full Fock space F(Q^n): X_i = l(e_i) + l(e_i)^*, tau = vacuum state;
  (B) the moment-cumulant formula for a free semicircular family: tau(s_{i1}...s_{im}) is the number
      of non-crossing pair partitions of [m] whose blocks are monochromatic (Voiculescu / Speicher);
  (C) closed form: ||s_1...s_d||_4^4 = Fuss-Catalan number binom(2d+2, 2)/(2d+1) = d + 1.
"""
from fractions import Fraction as F
from functools import lru_cache
from itertools import combinations, product
import math
import random
import sys

FAILS = 0


def check(cond, msg):
    global FAILS
    print(("PASS " if cond else "FAIL ") + msg)
    if not cond:
        FAILS += 1


# ---------------------------------------------------------------- Gaussian rationals
class G:
    """Exact complex number a + b i with a, b rational."""
    __slots__ = ("re", "im")

    def __init__(self, re, im=0):
        self.re, self.im = F(re), F(im)

    def __add__(self, o):
        o = o if isinstance(o, G) else G(o)
        return G(self.re + o.re, self.im + o.im)
    __radd__ = __add__

    def __mul__(self, o):
        o = o if isinstance(o, G) else G(o)
        return G(self.re * o.re - self.im * o.im, self.re * o.im + self.im * o.re)
    __rmul__ = __mul__

    def conj(self):
        return G(self.re, -self.im)

    def __eq__(self, o):
        o = o if isinstance(o, G) else G(o)
        return self.re == o.re and self.im == o.im

    def iszero(self):
        return self.re == 0 and self.im == 0

    def __repr__(self):
        return f"{self.re}+{self.im}i" if self.im else f"{self.re}"


# ---------------------------------------------------------------- (A) Fock space
# A vector is a dict {word (tuple of letters): coefficient}; the vacuum is the empty word.
OMEGA = {(): G(1)}


def add_to(acc, w, c):
    v = acc.get(w)
    acc[w] = c if v is None else v + c
    if acc[w].iszero():
        del acc[w]


def X(i, v):
    """X_i = creation l(e_i) + annihilation l(e_i)^*."""
    out = {}
    for w, c in v.items():
        add_to(out, (i,) + w, c)                 # l(e_i): w -> i w
        if w and w[0] == i:                      # l(e_i)^*: i w' -> w', kills Omega and j w', j != i
            add_to(out, w[1:], c)
    return out


def lin(op_terms, v):
    """Apply the operator  sum_k coef_k * X_{i_k1} ... X_{i_km}  (terms: list of (coef, letters))."""
    out = {}
    for coef, letters in op_terms:
        u = dict(v)
        for i in reversed(letters):
            u = X(i, u)
        for w, c in u.items():
            add_to(out, w, coef * c)
    return out


def adjoint(op_terms):
    """(c X_{i1}...X_{im})^* = conj(c) X_{im}...X_{i1}  (each X_i is self-adjoint)."""
    return [(G(c).conj() if not isinstance(c, G) else c.conj(), tuple(reversed(l))) for c, l in op_terms]


def inner(u, v):
    """<u, v>, conjugate-linear in u."""
    s = G(0)
    for w, c in u.items():
        if w in v:
            s = s + c.conj() * v[w]
    return s


def fock_norms(op_terms):
    """(||W||_2^2, ||W||_4^4) = (<W Omega, W Omega>, <W*W Omega, W*W Omega>)."""
    WO = lin(op_terms, OMEGA)
    WsWO = lin(adjoint(op_terms), WO)
    return inner(WO, WO), inner(WsWO, WsWO)


def tau_word(letters):
    return inner(OMEGA, lin([(G(1), tuple(letters))], OMEGA))


# ---------------------------------------------------------------- (B) non-crossing pairings
@lru_cache(maxsize=None)
def nc_count(colors):
    """Number of non-crossing pair partitions of positions 0..m-1 with monochromatic blocks."""
    m = len(colors)
    if m == 0:
        return 1
    if m % 2:
        return 0
    total = 0
    # position 0 is paired with position j; the inside (1..j-1) and outside (j+1..) are independent
    for j in range(1, m, 2):
        if colors[j] == colors[0]:
            total += nc_count(colors[1:j]) * nc_count(colors[j + 1:])
    return total


def catalan(k):
    return math.comb(2 * k, k) // (k + 1)


def f(d):
    return 2 - (1 - F(1, 2 ** d)) / d


def is_rational_square(q):
    q = F(q)
    if q < 0:
        return False
    a, b = math.isqrt(q.numerator), math.isqrt(q.denominator)
    return a * a == q.numerator and b * b == q.denominator


def v2(q):
    """2-adic valuation of a nonzero rational."""
    q = F(q)
    n, d, v = q.numerator, q.denominator, 0
    while n % 2 == 0:
        n //= 2; v += 1
    while d % 2 == 0:
        d //= 2; v -= 1
    return v


print("== 1. the semicircle law of X_0 on the Fock space")
mom = [tau_word([0] * k) for k in range(13)]
check(all(mom[k] == (catalan(k // 2) if k % 2 == 0 else 0) for k in range(13)),
      f"tau(X_0^k), k=0..12 = {[str(m) for m in mom]} (Catalan in even degree, 0 in odd)")
check(all(nc_count((0,) * k) == (catalan(k // 2) if k % 2 == 0 else 0) for k in range(13)),
      "NC pairings of [k] (one colour) agree")

print("\n== 2. mixed moments: Fock space vs non-crossing pairings (all words of length <= 8 in 3 letters)")
ok = True
cnt = 0
for m in range(0, 9):
    for word in product(range(3), repeat=m):
        cnt += 1
        if tau_word(word) != nc_count(word):
            ok = False
check(ok, f"{cnt} words: <Omega, X_w Omega> = #monochromatic NC pairings (free semicircular family)")

print("\n== 3. the free word W_d = s_1 s_2 ... s_d, d = 1..5")
for d in range(1, 6):
    W = [(G(1), tuple(range(d)))]
    n2, n4 = fock_norms(W)
    letters = tuple(reversed(range(d))) + tuple(range(d))
    nc2 = nc_count(letters)
    nc4 = nc_count(letters + letters)
    fuss = math.comb(2 * d + 2, 2) // (2 * d + 1)
    check(n2 == 1 and nc2 == 1 and n4 == d + 1 and nc4 == d + 1 and fuss == d + 1,
          f"d={d}: ||W||_2^2 = {n2} (NC: {nc2}), ||W||_4^4 = {n4} (NC: {nc4}, Fuss-Catalan {fuss}) = d+1")
    M4_4 = F(d + 1)          # M_4(d)^4
    fd = f(d)
    check(fd * fd != M4_4, f"   M_4^2 = f(d)?  f(d)^2 = {fd*fd} vs M_4^4 = {M4_4}: differ")
    check(fd != M4_4, f"   M_4^4 = f(d)?  f(d) = {fd} vs {M4_4}: differ")
    check(fd ** 4 != M4_4, f"   M_4   = f(d)?  f(d)^4 = {fd**4} vs {M4_4}: differ")
check(F(9, 4) != 2, "d = 1: (M_4(1)^2)^2 = 2  but  f(1)^2 = (3/2)^2 = 9/4")

print("\n== 4. all d (2-adic argument): f(d) has negative 2-adic valuation, M_4(d)^4 = d+1 is an integer")
ok = all(v2(f(d)) < 0 and f(d) < 2 and f(d) >= F(3, 2) for d in range(1, 200))
check(ok, "for d = 1..199: 3/2 <= f(d) < 2 and v_2(f(d)) = -(d + v_2(d)) < 0, so f(d), f(d)^2, f(d)^4 are never integers")
check(all(v2(f(d)) == -(d + v2(F(d))) for d in range(1, 200)), "v_2(f(d)) = -(d + v_2(d)) for d = 1..199")

print("\n== 5. first chaos (d = 1, optimal-constant reading): ratio tau(|S|^4)/tau(|S|^2)^2 = 2 always")
random.seed(7739)
ok = True
for trial in range(40):
    n = random.randint(1, 4)
    if trial % 2 == 0:
        coefs = [G(F(random.randint(-9, 9), random.randint(1, 5))) for _ in range(n)]          # real
    else:
        coefs = [G(F(random.randint(-9, 9), random.randint(1, 5)),
                   F(random.randint(-9, 9), random.randint(1, 5))) for _ in range(n)]       # complex
    if all(c.iszero() for c in coefs):
        continue
    S = [(c, (i,)) for i, c in enumerate(coefs)]
    n2, n4 = fock_norms(S)
    if not (n4 == 2 * n2 * n2):
        ok = False
check(ok, "40 random S = sum a_i s_i (real and complex a_i, up to 4 generators): ||S||_4^4 = 2 ||S||_2^4")
# circular element c = (s1 + i s2)/sqrt2 (scaled by sqrt2 to stay rational) and elliptic family
n2, n4 = fock_norms([(G(1), (0,)), (G(0, 1), (1,))])
check(n4 == 2 * n2 * n2, f"circular s1 + i s2: ||.||_2^2 = {n2}, ||.||_4^4 = {n4}, ratio 2")
ok = True
for a, b in [(1, 2), (3, 1), (2, 5), (7, 3)]:
    n2, n4 = fock_norms([(G(a), (0,)), (G(0, b), (1,))])
    ok = ok and n4 == 2 * n2 * n2
check(ok, "elliptic elements a s1 + i b s2: ratio 2 for several (a, b)")

print("\n== 6. higher chaoses: ratio >= 2, sup >= d+1, inf = 2 (so no extremal reading gives f(d)^2)")
# second chaos I(h) = sum h_ij (s_i s_j - delta_ij), random complex h on 2 or 3 generators
ok = True
mn = None
for trial in range(25):
    n = random.choice([2, 3])
    terms = []
    for i in range(n):
        for j in range(n):
            h = G(F(random.randint(-5, 5), random.randint(1, 3)), F(random.randint(-5, 5), random.randint(1, 3)))
            terms.append((h, (i, j)))
            if i == j:
                terms.append((G(-1) * h, ()))
    n2, n4 = fock_norms(terms)
    if n2.iszero():
        continue
    r = n4.re / (n2.re * n2.re)
    ok = ok and n4.im == 0 and r >= 2
    mn = r if mn is None else min(mn, r)
check(ok, f"25 random elements of the 2nd chaos: ratio >= 2 (smallest seen {float(mn):.4f})")
n2, n4 = fock_norms([(G(1), (0, 0)), (G(-1), ())])
check(n2 == 1 and n4 == 3, "s^2 - 1 (2nd chaos, self-adjoint): ||.||_2^2 = 1, ||.||_4^4 = 3")
# W_n = sum_{j<n} w_j with w_j = s_{j,1}...s_{j,d}: ratio 2 + (d-1)/n  -> 2
ok = True
for d in (2, 3):
    for nn in (1, 2, 3):
        terms = [(G(1), tuple(range(j * d, j * d + d))) for j in range(nn)]
        n2, n4 = fock_norms(terms)
        r = n4.re / (n2.re * n2.re)
        ok = ok and n2 == nn and r == 2 + F(d - 1, nn)
check(ok, "W_n = sum of n free copies of s_1...s_d: ratio = 2 + (d-1)/n for d = 2,3, n = 1,2,3")
check(all(F(d + 1) > f(d) ** 2 > 2 for d in range(2, 200)) and f(1) ** 2 > 2,
      "for d = 2..199: inf ratio = 2 < f(d)^2 < d + 1 <= sup ratio; at d = 1 the ratio is 2 < 9/4 = f(1)^2")

print("\n== 7. Haar unitary / free group reading")
# x = sum_s a_s lambda(s), s in generators and inverses of a free group (letters (gen, +-1))


def reduce_word(w):
    out = []
    for x in w:
        if out and out[-1][0] == x[0] and out[-1][1] == -x[1]:
            out.pop()
        else:
            out.append(x)
    return tuple(out)


def fg_ratio(coef):
    """coef: dict {(gen, eps): complex G}; returns tau(|x|^4)/tau(|x|^2)^2 for x = sum coef lambda(s)."""
    items = list(coef.items())
    xs = [((g, -e), c.conj()) for (g, e), c in items]    # x^* = sum conj(a_s) lambda(s^{-1})
    x = [((g, e), c) for (g, e), c in items]
    t2 = G(0)
    for (s1, c1), (s2, c2) in product(xs, x):
        if reduce_word((s1, s2)) == ():
            t2 = t2 + c1 * c2
    t4 = G(0)
    for (s1, c1), (s2, c2), (s3, c3), (s4, c4) in product(xs, x, xs, x):
        if reduce_word((s1, s2, s3, s4)) == ():
            t4 = t4 + c1 * c2 * c3 * c4
    return t4.re / (t2.re ** 2), t2, t4


r, _, _ = fg_ratio({(0, 1): G(1)})
check(r == 1, "a single Haar unitary u (= any word in free group generators): |u| = 1, M_4 = 1")
r, t2, t4 = fg_ratio({(0, 1): G(1), (0, -1): G(1)})
check(t2 == 2 and t4 == 6 and r == F(3, 2), "u + u^*: tau 2nd = 2, 4th = 6, ratio 3/2 (so M_4^2 = sqrt(3/2) != 3/2)")
ok = True
for trial in range(30):
    coef = {}
    for g in range(random.randint(1, 3)):
        for e in (1, -1):
            if random.random() < 0.7:
                coef[(g, e)] = G(random.randint(-4, 4), random.randint(-4, 4))
    coef = {k: v for k, v in coef.items() if not v.iszero()}
    if not coef:
        continue
    r, t2, _ = fg_ratio(coef)
    beta = sum((c.re ** 2 + c.im ** 2) for c in coef.values())
    pred = 2 - sum((c.re ** 2 + c.im ** 2) ** 2 for c in coef.values()) / beta ** 2
    ok = ok and r == pred and 1 <= r < 2
check(ok, "30 random x = sum a_s lambda(s): ratio = 2 - sum|a_s|^4/(sum|a_s|^2)^2 in [1, 2), never 9/4")

print("\n== 8. disclosed coincidence: the NON-centred element 1 + s (not a free word)")
n2, n4 = fock_norms([(G(1), ()), (G(1), (0,))])
check(n2 == 2 and n4 == 9 and F(9, 4) == f(1) ** 2,
      "1 + s: tau((1+s)^2) = 2, tau((1+s)^4) = 1 + 6 + 2 = 9, ratio 9/4 = f(1)^2 (so M_4^2 = 3/2 = f(1))")
# optimal constant over x = a + sum c_i s_i: ratio = g(t) = (t^2+6t+2)/(t+1)^2 at most, t = |a|^2/|c|^2
g = lambda t: (t * t + 6 * t + 2) / (t + 1) ** 2
ok = all(g(F(p, q)) <= F(7, 3) for p in range(0, 60) for q in range(1, 20))
n2, n4 = fock_norms([(G(1), ()), (G(1), (0,)), (G(1), (1,))])      # a = 1, |c|^2 = 2, t = 1/2
ok = ok and g(F(1, 2)) == F(7, 3) and n4.re / n2.re ** 2 == F(7, 3)
for trial in range(60):                                              # random complex a, c_i
    n = random.randint(1, 3)
    a = G(F(random.randint(-6, 6), random.randint(1, 3)), F(random.randint(-6, 6), random.randint(1, 3)))
    cs = [G(F(random.randint(-6, 6), random.randint(1, 3)), F(random.randint(-6, 6), random.randint(1, 3)))
          for _ in range(n)]
    terms = [(a, ())] + [(c, (i,)) for i, c in enumerate(cs)]
    n2, n4 = fock_norms(terms)
    if n2.iszero():
        continue
    A = a.re ** 2 + a.im ** 2
    B = sum(c.re ** 2 + c.im ** 2 for c in cs)
    r = n4.re / n2.re ** 2
    ok = ok and r <= F(7, 3) and (B == 0 or r <= g(A / B))
check(ok, "sup over x = a + sum c_i s_i (complex) of ||x||_4^4/||x||_2^4 is 7/3 (attained at |a|^2/|c|^2 = 1/2), not 9/4")
ok = True
vals = []
for d in range(1, 5):
    n2, n4 = fock_norms([(G(1), ()), (G(1), tuple(range(d)))])
    r1 = n4.re / n2.re ** 2
    terms = [(G(1), tuple(S)) for k in range(d + 1) for S in combinations(range(d), k)]
    n2, n4 = fock_norms(terms)
    r2 = n4.re / n2.re ** 2
    vals.append((d, r1, r2))
    ok = ok and r2 == 1 + F(5 * d, 4) and (d == 1 or r1 == F(d + 6, 4))
    if d >= 2:
        ok = ok and all(r not in (f(d), f(d) ** 2, f(d) ** 4) for r in (r1, r2))
check(ok, "length-d extensions: ratio(1 + s_1...s_d) = 9/4, 2, 9/4, 5/2 (= (d+6)/4 for d >= 2); "
          "ratio(prod (1+s_i)) = 1 + 5d/4; for d = 2..4 neither equals f(d), f(d)^2 or f(d)^4 "
          f"(f(2)^2 = 169/64); values {[(d, str(a), str(b)) for d, a, b in vals]}")

print("\n== 9. further Haar-unitary / free-group analogues (group algebra, exact)")
# group elements: reduced tuples of (generator, exponent); generators in INVOL have order 2


def gmul(w1, w2, invol):
    out = list(w1)
    for x in w2:
        if out and out[-1][0] == x[0] and (x[0] in invol or out[-1][1] == -x[1]):
            out.pop()
        else:
            out.append(x)
    return tuple(out)


def ginv(w, invol):
    return tuple((g, e if g in invol else -e) for g, e in reversed(w))


def amul(x, y, invol):
    out = {}
    for w1, c1 in x.items():
        for w2, c2 in y.items():
            w = gmul(w1, w2, invol)
            out[w] = out.get(w, 0) + c1 * c2
    return {w: c for w, c in out.items() if c != 0}


def gratio(x, invol=()):
    """tau(|x|^4)/tau(|x|^2)^2 in the group von Neumann algebra (real coefficients)."""
    xs = {ginv(w, invol): c for w, c in x.items()}
    y = amul(xs, x, invol)                       # x^* x, self-adjoint
    t2 = F(y.get((), 0))
    t4 = sum(F(c) * c for c in y.values())       # tau(y^2) = sum |y_w|^2
    return t4 / t2 ** 2


def reduced_words(gens, d, invol):
    letters = [(g, 1) for g in gens] + [(g, -1) for g in gens if g not in invol]
    words = [()]
    for _ in range(d):
        words = [w + (l,) for w in words for l in letters if gmul(w, (l,), invol) == w + (l,)]
    return words


ok = True
for d in range(1, 5):
    x = {}
    for i in range(d):
        x[((i, 1),)] = 1
        x[((i, -1),)] = 1
    ok = ok and gratio(x) == 2 - F(1, 2 * d)
check(ok, "sum_{i<=d} (u_i + u_i^*): ratio 2 - 1/(2d), d = 1..4")
ok = True
for d in range(1, 4):
    x = {(): 1}
    for i in range(d):
        x = amul(x, {((i, 1),): 1, ((i, -1),): 1}, ())
    ok = ok and gratio(x) == 1 + F(d, 2)
check(ok, "prod_{i<=d} (u_i + u_i^*): ratio 1 + d/2, d = 1..3")
ok = True
for d in range(1, 5):
    ok = ok and gratio({((i, 1),): 1 for i in range(d)}, invol=tuple(range(d))) == 2 - F(1, d)
check(ok, "free Bernoulli sums b_1 + ... + b_d (b_i free symmetric +-1): ratio 2 - 1/d, d = 1..4")
ok = True
rad = []
for d in range(1, 4):
    r_f = gratio({w: 1 for w in reduced_words((0, 1), d, ())})
    r_z = gratio({w: 1 for w in reduced_words((0, 1, 2), d, (0, 1, 2))}, invol=(0, 1, 2))
    rad.append((d, str(r_f), str(r_z)))
    if d >= 2:
        ok = ok and all(r not in (f(d), f(d) ** 2, f(d) ** 4) for r in (r_f, r_z))
check(ok, f"sum of all reduced words of length d in F_2 and in Z_2*Z_2*Z_2 (d, F_2, Z_2^*3) = {rad}: "
          "none equals f(d), f(d)^2, f(d)^4 for d = 2, 3")
ok = all(r not in (f(d), f(d) ** 2, f(d) ** 4)
         for d in range(2, 30) for r in (2 - F(1, 2 * d), 1 + F(d, 2), 2 - F(1, d)))
check(ok, "for d = 2..29 the three closed forms 2-1/(2d), 1+d/2, 2-1/d never equal f(d), f(d)^2, f(d)^4")

print()
if FAILS:
    print(f"{FAILS} check(s) FAILED")
    sys.exit(1)
print("ALL CHECKS PASSED: M_4(1)^4 = 2 but f(1)^2 = 9/4; the clause M_4(d)^2 = 2 - (1-2^-d)/d is false.")
