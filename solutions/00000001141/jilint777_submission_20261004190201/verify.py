#!/usr/bin/env python3
"""Independent check for conjecture 00000001141 (Python 3 standard library only).

Claim refuted: "the Krull dimension of the centre of u(sl_n) is n - 1" (n = 2: claimed 1).

Method (independent of the Lean development, which works with fixed operator tables):
  * u(sl_2) over F_p is rebuilt from scratch from the defining relations by a *word-rewriting*
    normal-ordering procedure (he -> eh + 2e, fe -> ef - h, fh -> hf + 2f, e^p -> 0, f^p -> 0,
    h^p -> h), for p = 2, 3, 5.
  * The multiplication table on the PBW basis e^a h^b f^c (0 <= a, b, c < p) is checked for
    associativity, unit and the defining relations.
  * The centre Z is computed by Gaussian elimination over F_p; its dimension is compared with the
    rank of sl_2 (= 1).
  * The prime ideals of Z are computed: for p = 2, 3 by brute force over all F_p-subspaces of Z
    (every ideal is one), for p = 5 via the nilradical and the Frobenius.  In every case there is
    no strict inclusion P < Q of prime ideals, i.e. Krull dim Z = 0, not 1.
  * Reading "U(sl_n) in characteristic p": the p-centre elements e^p, f^p, h^p - h are checked to
    be central in the full enveloping algebra U(sl_2) over F_p (so Krull dim Z(U) = dim sl_2 = 3).
  * The operator tables used in lean4/Main.lean are re-derived and compared.
"""
import itertools
import os
import re
import sys
from functools import lru_cache

FAIL = 0


def check(cond, msg):
    global FAIL
    print(("PASS " if cond else "FAIL ") + msg)
    if not cond:
        FAIL += 1


# ---------------------------------------------------------------------------
# 1. Normal ordering by word rewriting
# ---------------------------------------------------------------------------

def make_normalizer(p, restricted=True):
    """Return norm(word) -> dict {(a,b,c): coeff mod p} for words in 'e','h','f'."""

    @lru_cache(maxsize=None)
    def norm(w):
        # find the first adjacent pair out of the order e < h < f
        for i in range(len(w) - 1):
            x, y = w[i], w[i + 1]
            pre, post = w[:i], w[i + 2:]
            if (x, y) == ('h', 'e'):      # he = eh + 2e
                return add(norm(pre + 'eh' + post), norm(pre + 'e' + post), 1, 2)
            if (x, y) == ('f', 'e'):      # fe = ef - h
                return add(norm(pre + 'ef' + post), norm(pre + 'h' + post), 1, -1)
            if (x, y) == ('f', 'h'):      # fh = hf + 2f
                return add(norm(pre + 'hf' + post), norm(pre + 'f' + post), 1, 2)
        a, b, c = w.count('e'), w.count('h'), w.count('f')
        if restricted:
            if a >= p or c >= p:          # e^p = 0, f^p = 0
                return {}
            if b >= p:                    # h^p = h
                return norm('e' * a + 'h' * (b - p + 1) + 'f' * c)
        return {(a, b, c): 1}

    def add(d1, d2, s1, s2):
        out = {}
        for k, v in d1.items():
            out[k] = (out.get(k, 0) + s1 * v) % p
        for k, v in d2.items():
            out[k] = (out.get(k, 0) + s2 * v) % p
        return {k: v for k, v in out.items() if v}

    return norm


def word(t):
    a, b, c = t
    return 'e' * a + 'h' * b + 'f' * c


class RestrictedSl2:
    def __init__(self, p):
        self.p = p
        self.B = [(a, b, c) for a in range(p) for b in range(p) for c in range(p)]
        self.N = len(self.B)
        self.idx = {t: i for i, t in enumerate(self.B)}
        norm = make_normalizer(p)
        N = self.N
        # left multiplication by the generators, from rewriting g * (e^a h^b f^c)
        self.L = {}
        self.R = {}
        for g in 'ehf':
            self.L[g] = [self.vec(norm(g + word(t))) for t in self.B]
            self.R[g] = [self.vec(norm(word(t) + g)) for t in self.B]
        # full table b_i * b_j = e^a h^b f^c . b_j, computed by applying left multiplications
        self.prod = [[None] * N for _ in range(N)]
        for j in range(N):
            # mono(a,b,c) . b_j = L_e^a L_h^b L_f^c b_j
            col = {}
            bj = self.unit(j)
            for c in range(p):
                vf = bj if c == 0 else self.apply('f', col[(0, 0, c - 1)])
                col[(0, 0, c)] = vf
                for b in range(p):
                    vh = vf if b == 0 else self.apply('h', col[(0, b - 1, c)])
                    col[(0, b, c)] = vh
                    for a in range(1, p):
                        col[(a, b, c)] = self.apply('e', col[(a - 1, b, c)])
            for i, t in enumerate(self.B):
                self.prod[i][j] = col[t]
        self.norm = norm

    def vec(self, d):
        v = [0] * self.N
        for k, c in d.items():
            v[self.idx[k]] = c % self.p
        return v

    def unit(self, i):
        v = [0] * self.N
        v[i] = 1
        return v

    def apply(self, g, v):
        out = [0] * self.N
        for j, x in enumerate(v):
            if x:
                col = self.L[g][j]
                for k, y in enumerate(col):
                    if y:
                        out[k] = (out[k] + x * y) % self.p
        return out

    def mul(self, x, y):
        p, N = self.p, self.N
        out = [0] * N
        for i, xi in enumerate(x):
            if not xi:
                continue
            row = self.prod[i]
            for j, yj in enumerate(y):
                if not yj:
                    continue
                c = xi * yj
                for k, z in enumerate(row[j]):
                    if z:
                        out[k] = (out[k] + c * z) % p
        return out

    def add(self, x, y, s=1):
        return [(a + s * b) % self.p for a, b in zip(x, y)]

    def smul(self, c, x):
        return [(c * a) % self.p for a in x]


def nullspace(rows, n, p):
    rows = [r[:] for r in rows]
    piv = []
    r = 0
    for c in range(n):
        pr = next((i for i in range(r, len(rows)) if rows[i][c] % p), None)
        if pr is None:
            continue
        rows[r], rows[pr] = rows[pr], rows[r]
        inv = pow(rows[r][c], p - 2, p)
        rows[r] = [x * inv % p for x in rows[r]]
        for i in range(len(rows)):
            if i != r and rows[i][c] % p:
                f = rows[i][c]
                rows[i] = [(x - f * y) % p for x, y in zip(rows[i], rows[r])]
        piv.append(c)
        r += 1
    free = [c for c in range(n) if c not in piv]
    basis = []
    for fc in free:
        v = [0] * n
        v[fc] = 1
        for i, pc in enumerate(piv):
            v[pc] = (-rows[i][fc]) % p
        basis.append(v)
    return basis


def rank(rows, n, p):
    return n - len(nullspace(rows, n, p)) if rows else 0


def all_subspaces(d, p):
    """All subspaces of F_p^d, as lists of basis vectors in reduced row echelon form."""
    out = []
    for k in range(d + 1):
        for pivots in itertools.combinations(range(d), k):
            free_pos = [(r, c) for r in range(k) for c in range(d)
                        if c > pivots[r] and c not in pivots]
            for vals in itertools.product(range(p), repeat=len(free_pos)):
                rows = [[0] * d for _ in range(k)]
                for r in range(k):
                    rows[r][pivots[r]] = 1
                for (r, c), v in zip(free_pos, vals):
                    rows[r][c] = v
                out.append(rows)
    return out


def span(rows, d, p):
    S = set()
    for coeffs in itertools.product(range(p), repeat=len(rows)):
        v = [0] * d
        for c, r in zip(coeffs, rows):
            if c:
                v = [(a + c * b) % p for a, b in zip(v, r)]
        S.add(tuple(v))
    return S


# ---------------------------------------------------------------------------
# 2. Checks
# ---------------------------------------------------------------------------

def run(p, brute_primes, full_assoc):
    print(f"--- p = {p} ---")
    U = RestrictedSl2(p)
    N = U.N
    check(N == p ** 3, f"[p={p}] PBW basis e^a h^b f^c has {N} = p^3 = p^(dim sl_2) elements")
    one = U.unit(U.idx[(0, 0, 0)])
    e, h, f = (U.unit(U.idx[t]) for t in [(1, 0, 0), (0, 1, 0), (0, 0, 1)])
    # products of basis monomials agree with direct rewriting of the concatenated word
    sample = list(range(N)) if N <= 27 else list(range(0, N, 7))
    ok = all(U.prod[i][j] == U.vec(U.norm(word(U.B[i]) + word(U.B[j])))
             for i in sample for j in sample)
    check(ok, f"[p={p}] multiplication table = rewriting of concatenated words (checked pairs)")
    # unit and associativity
    check(all(U.mul(one, U.unit(i)) == U.unit(i) == U.mul(U.unit(i), one) for i in range(N)),
          f"[p={p}] 1 is a two-sided unit")
    if full_assoc:
        ok = True
        for i in range(N):
            for j in range(N):
                ij = U.prod[i][j]
                for k in range(N):
                    if U.mul(ij, U.unit(k)) != U.mul(U.unit(i), U.prod[j][k]):
                        ok = False
                        break
        check(ok, f"[p={p}] associativity on all {N**3} basis triples")
    else:
        ok = True
        for g in (e, h, f):
            for j in range(N):
                gj = U.mul(g, U.unit(j))
                for k in range(N):
                    if U.mul(gj, U.unit(k)) != U.mul(g, U.prod[j][k]):
                        ok = False
        check(ok, f"[p={p}] (g x) y = g (x y) for g in {{e,h,f}} and all basis x, y "
                  f"(implies associativity, the algebra being generated by e, h, f)")
    # defining relations
    def br(x, y):
        return U.add(U.mul(x, y), U.mul(y, x), -1)

    def pw(x, n):
        r = one
        for _ in range(n):
            r = U.mul(r, x)
        return r
    check(br(h, e) == U.smul(2, e), f"[p={p}] [h,e] = 2e")
    check(br(h, f) == U.smul(-2, f), f"[p={p}] [h,f] = -2f")
    check(br(e, f) == h, f"[p={p}] [e,f] = h")
    check(pw(e, p) == [0] * N and pw(f, p) == [0] * N and pw(h, p) == h,
          f"[p={p}] e^p = 0, f^p = 0, h^p = h (restricted relations)")
    # PBW monomials are the products e^a h^b f^c
    ok = all(U.mul(U.mul(pw(e, a), pw(h, b)), pw(f, c)) == U.unit(U.idx[(a, b, c)])
             for (a, b, c) in U.B)
    check(ok, f"[p={p}] the basis vector (a,b,c) is the product e^a h^b f^c")

    # centre
    rows = []
    for g in (e, h, f):
        gi = U.idx[(1, 0, 0)] if g is e else U.idx[(0, 1, 0)] if g is h else U.idx[(0, 0, 1)]
        for k in range(N):
            rows.append([(U.prod[i][gi][k] - U.prod[gi][i][k]) % p for i in range(N)])
    Zb = nullspace(rows, N, p)
    d = len(Zb)
    expected = (3 * p - 1) // 2 if p > 2 else 5
    check(d == expected, f"[p={p}] dim_F_p Z(u(sl_2)) = {d}"
                         + (f" = (3p-1)/2" if p > 2 else "") + "  (rank sl_2 = 1)")
    check(d != 1, f"[p={p}] dim Z = {d} != 1 = rank(sl_2): the 'dimension = rank' reading fails")
    # Casimir C = ef + fe + h^2/2 (p odd) is central and not a scalar
    if p > 2:
        inv2 = pow(2, p - 2, p)
        C = U.add(U.add(U.mul(e, f), U.mul(f, e)), U.smul(inv2, U.mul(h, h)))
        check(all(U.mul(C, g) == U.mul(g, C) for g in (e, h, f)) and
              any(C[i] for i in range(N) if i != U.idx[(0, 0, 0)]),
              f"[p={p}] Casimir ef + fe + h^2/2 is central and not a scalar")
    # Z is a commutative subalgebra; structure constants in the basis Zb
    zprod = {}
    Zrows = [list(z) for z in Zb]
    for a in range(d):
        for b in range(d):
            prod = U.mul(Zb[a], Zb[b])
            # express prod in the basis Zb: solve sum c_i Zb_i = prod
            M = [[Zb[i][k] for i in range(d)] + [prod[k]] for k in range(N)]
            sol = nullspace(M, d + 1, p)
            coeffs = None
            for s in sol:
                if s[d] % p:
                    inv = pow(s[d], p - 2, p)
                    coeffs = [(-x * inv) % p for x in s[:d]]
                    break
            if coeffs is None and all(x == 0 for x in prod):
                coeffs = [0] * d
            zprod[(a, b)] = coeffs
    check(all(zprod[(a, b)] is not None for a in range(d) for b in range(d)),
          f"[p={p}] Z is closed under multiplication")
    check(all(zprod[(a, b)] == zprod[(b, a)] for a in range(d) for b in range(d)),
          f"[p={p}] Z is commutative")
    unit_coords = None
    M = [[Zb[i][k] for i in range(d)] + [one[k]] for k in range(N)]
    for s in nullspace(M, d + 1, p):
        if s[d] % p:
            inv = pow(s[d], p - 2, p)
            unit_coords = [(-x * inv) % p for x in s[:d]]

    def zmul(x, y):
        out = [0] * d
        for a, xa in enumerate(x):
            if xa:
                for b, yb in enumerate(y):
                    if yb:
                        for k, c in enumerate(zprod[(a, b)]):
                            if c:
                                out[k] = (out[k] + xa * yb * c) % p
        return out

    if brute_primes:
        elems = [list(t) for t in itertools.product(range(p), repeat=d)]
        multab = {}
        for x in elems:
            for y in elems:
                multab[(tuple(x), tuple(y))] = tuple(zmul(x, y))
        subspaces = all_subspaces(d, p)
        ideals, primes = [], []
        for rows_ in subspaces:
            S = span(rows_, d, p)
            # ideal: closed under multiplication by the basis of Z (and it is a subspace)
            if not all(tuple(zmul(list(s), [1 if i == a else 0 for i in range(d)])) in S
                       for s in S for a in range(d)):
                continue
            ideals.append(S)
            if tuple(unit_coords) in S:
                continue
            if all(multab[(tuple(x), tuple(y))] not in S or tuple(x) in S or tuple(y) in S
                   for x in elems for y in elems):
                primes.append(S)
        print(f"INFO [p={p}] Z has {p**d} elements, {len(subspaces)} subspaces, "
              f"{len(ideals)} ideals, {len(primes)} prime ideals "
              f"(sizes {sorted(len(P) for P in primes)})")
        chain = any(P < Q for P in primes for Q in primes)
        check(len(primes) >= 1 and not chain,
              f"[p={p}] brute force: no strict inclusion P < Q of prime ideals of Z, "
              f"so Krull dim Z = 0 (claimed 1)")
        maximal = all(not any(S > P and len(S) < p ** d for S in ideals) for P in primes)
        check(maximal, f"[p={p}] every prime ideal of Z is maximal")
    else:
        # Frobenius F(z) = z^p is F_p-linear on the commutative F_p-algebra Z.
        def frob(z):
            r = unit_coords
            for _ in range(p):
                r = zmul(r, z)
            return r
        # nilradical = kernel of F^k for p^k >= d
        k = 1
        while p ** k < d + 1:
            k += 1

        def frobk(z):
            for _ in range(k):
                z = frob(z)
            return z
        img = [frobk([1 if i == a else 0 for i in range(d)]) for a in range(d)]
        nil = nullspace([[img[a][r] for a in range(d)] for r in range(d)], d, p)
        # reduced quotient Z/N = product of finite fields; number of factors = dim{z : z^p = z}
        fix = nullspace([[(frob([1 if i == a else 0 for i in range(d)])[r]
                           - (1 if r == a else 0)) % p for a in range(d)] for r in range(d)],
                        d, p)
        fixN = rank([list(v) for v in fix] + [list(v) for v in nil], d, p) - len(nil)
        print(f"INFO [p={p}] dim nilradical = {len(nil)}, dim Z/N = {d - len(nil)}, "
              f"number of prime (= maximal) ideals = {fixN}")
        check(fixN == d - len(nil),
              f"[p={p}] Z/nilradical is a product of {fixN} copies of F_p, so Z has exactly "
              f"{fixN} prime ideals, all maximal, pairwise incomparable: Krull dim Z = 0")
    return U


def check_U_pcentre(p):
    """In the full U(sl_2) over F_p, e^p, f^p and h^p - h are central."""
    norm = make_normalizer(p, restricted=False)

    def mulw(w1, w2):
        return norm(w1 + w2)

    def sub(d1, d2):
        out = dict(d1)
        for k, v in d2.items():
            out[k] = (out.get(k, 0) - v) % p
        return {k: v for k, v in out.items() if v}
    ok = True
    for z in ('e' * p, 'f' * p):
        for g in 'ehf':
            if sub(mulw(z, g), mulw(g, z)):
                ok = False
    for g in 'ehf':
        lhs = sub(mulw('h' * p, g), mulw('h', g))
        rhs = sub(mulw(g, 'h' * p), mulw(g, 'h'))
        if sub(lhs, rhs):
            ok = False
    check(ok, f"[U(sl_2), p={p}] e^p, f^p, h^p - h are central in the full enveloping algebra "
              f"(p-centre Z_p = F_p[e^p, f^p, h^p - h], Krull dim 3 = dim sl_2)")


def check_lean_tables(U):
    path = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'lean4', 'Main.lean')
    if not os.path.exists(path):
        print("INFO lean4/Main.lean not found, table comparison skipped")
        return
    src = open(path, encoding='utf-8').read()
    ok = True
    for name, g, side in [('E', 'e', 'L'), ('H', 'h', 'L'), ('F', 'f', 'L'),
                          ('RE', 'e', 'R'), ('RH', 'h', 'R'), ('RF', 'f', 'R')]:
        m = re.search(r'def tbl' + name + r' : List \(List \(Nat × Nat\)\) :=\s*\[(.*?)\]\n',
                      src, re.S)
        if not m:
            ok = False
            continue
        rows = re.findall(r'\[([^\[\]]*)\]', m.group(1))
        cols = (U.L if side == 'L' else U.R)[g]
        for k, row in enumerate(rows):
            pairs = [tuple(map(int, x)) for x in re.findall(r'\((\d+), (\d+)\)', row)]
            mine = [(j, cols[j][k]) for j in range(U.N) if cols[j][k]]
            if sorted(pairs) != mine:
                ok = False
        if len(rows) != U.N:
            ok = False
    check(ok, "[p=3] the six operator tables in lean4/Main.lean equal the left/right "
              "multiplications by e, h, f obtained here by rewriting")


def main():
    run(2, brute_primes=True, full_assoc=True)
    U3 = run(3, brute_primes=True, full_assoc=True)
    run(5, brute_primes=False, full_assoc=False)
    for p in (2, 3, 5):
        check_U_pcentre(p)
    check_lean_tables(U3)
    print()
    if FAIL:
        print(f"{FAIL} CHECK(S) FAILED")
        sys.exit(1)
    print("ALL CHECKS PASSED: Krull dim Z(u(sl_2)) = 0 for p = 2, 3, 5, never n - 1 = 1;")
    print("dim_F_p Z(u(sl_2)) = 5, 4, 7 for p = 2, 3, 5, never rank(sl_2) = 1.")


if __name__ == '__main__':
    main()
