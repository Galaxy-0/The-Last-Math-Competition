#!/usr/bin/env python3
"""Independent check for conjecture 00000003831 (Python 3 standard library only).

Clause 1 of the conjecture: "for any finite crystal B, the coefficients of the Schur expansion
of the Weyl symmetrization of ch(B) are nonnegative".

Checks
  1. The 7-vertex gl_3 crystal B7 (B(2,1,0) with one weight-(1,1,1) vertex removed and the
     strings re-glued) satisfies all of Kashiwara's crystal axioms and is seminormal
     (eps_i, phi_i are the string lengths).  Sanity: B(1,0,0), B(2,1,0) and the word crystal
     B(1)^{(x)3} (tensor rule) pass the same checker.
  2. ch(B7) = m_210 + m_111.  Schur polynomials are computed in two independent ways:
     (a) from semistandard Young tableaux, (b) from the bialternant a_{lam+rho}/a_rho
     (exact polynomial division).  Both agree; ch(B7) = s_210 - s_111.
  3. All symmetrization readings: Weyl symmetrizer J(x^rho f)/J(x^rho) (computed by exact
     division), orbit sum, orbit average (Fractions).  Schur coefficients: -1, -6, -1 at s_111.
  4. Characters of finite seminormal crystals are exactly the W-invariant weight multisets
     satisfying the string condition; the realisation is constructed and re-checked.
     gl_2: every such character is Schur positive (exhaustive, <= 10 vertices, all weights).
     gl_3: no non-Schur-positive one has <= 6 vertices; with 7 vertices they exist.
  5. Remark: the 1-vertex abstract (non-seminormal) gl_2 crystal also violates clause 1.
"""
from itertools import permutations, product
from collections import Counter
from fractions import Fraction
import sys

OK = True


def check(cond, msg):
    global OK
    print(("PASS " if cond else "FAIL ") + msg)
    if not cond:
        OK = False


# ------------------------------------------------------------------ Laurent polynomials
# A polynomial in x_1..x_r is a dict {exponent tuple: nonzero coefficient}.
def clean(p):
    return {e: c for e, c in p.items() if c != 0}


def padd(*ps):
    r = Counter()
    for p in ps:
        for e, c in p.items():
            r[e] += c
    return clean(r)


def pscale(k, p):
    return clean({e: k * c for e, c in p.items()})


def pmul(p, q):
    r = Counter()
    for e1, c1 in p.items():
        for e2, c2 in q.items():
            r[tuple(a + b for a, b in zip(e1, e2))] += c1 * c2
    return clean(r)


def sign(perm):
    s = 1
    for a in range(len(perm)):
        for b in range(a + 1, len(perm)):
            if perm[a] > perm[b]:
                s = -s
    return s


def act(perm, p):
    """w acts by permuting variables: (w.x^e) = x^{e o w^{-1}}; exponent e -> (e[perm[k]])_k."""
    return {tuple(e[perm[k]] for k in range(len(e))): c for e, c in p.items()}


def J(p, r):
    return padd(*[pscale(sign(w), act(w, p)) for w in permutations(range(r))])


def rho(r):
    return tuple(range(r - 1, -1, -1))


def mono(e):
    return {tuple(e): 1}


def pdiv(num, den):
    """exact division of Laurent polynomials (lex-leading-term long division); None if inexact"""
    num = dict(num)
    q = {}
    lead_d = max(den)
    for _ in range(10000):
        if not num:
            return q
        lead_n = max(num)
        c, rem = divmod(num[lead_n], den[lead_d])
        if rem:
            return None
        e = tuple(a - b for a, b in zip(lead_n, lead_d))
        q[e] = q.get(e, 0) + c
        num = padd(num, pscale(-c, pmul(mono(e), den)))
    return None


def is_symmetric(p, r):
    return all(act(w, p) == p for w in permutations(range(r)))


# ---------------------------------------------------------------- Schur polynomials
def ssyt(shape, r):
    """all semistandard tableaux of the given shape with entries 1..r (brute force fillings)"""
    cells = [(i, j) for i, l in enumerate(shape) for j in range(l)]
    out = []
    for vals in product(range(1, r + 1), repeat=len(cells)):
        T = dict(zip(cells, vals))
        if all(T[(i, j)] <= T[(i, j + 1)] for (i, j) in cells if (i, j + 1) in T) and \
           all(T[(i, j)] < T[(i + 1, j)] for (i, j) in cells if (i + 1, j) in T):
            out.append(T)
    return out


def schur_ssyt(lam, r):
    """s_lam for a partition lam (nonnegative, weakly decreasing, length r) from SSYT;
    general dominant weights are handled by the det-shift s_{lam+k} = (x1..xr)^k s_lam."""
    k = lam[-1]
    shape = [l - k for l in lam if l - k > 0]
    p = Counter()
    for T in ssyt(shape, r):
        e = [k] * r
        for v in T.values():
            e[v - 1] += 1
        p[tuple(e)] += 1
    return dict(p)


def schur_bialt(lam, r):
    rh = rho(r)
    return pdiv(J(mono(tuple(a + b for a, b in zip(lam, rh))), r), J(mono(rh), r))


def schur_expand_bialt(f, r):
    """Schur coefficients of the Weyl symmetrization pi(f) = J(x^rho f)/J(x^rho):
    c_lam = coefficient of x^{lam+rho} in J(x^rho f), lam+rho strictly decreasing."""
    rh = rho(r)
    A = J(pmul(mono(rh), f), r)
    return {tuple(a - b for a, b in zip(e, rh)): c for e, c in A.items()
            if all(e[k] > e[k + 1] for k in range(r - 1))}


def schur_expand_peel(f, r):
    """independent method: repeatedly subtract c * s_lam (SSYT) for the lex-largest monomial
    (necessarily dominant for a symmetric f).  Requires f symmetric."""
    f = dict(f)
    res = {}
    while f:
        lead = max(f)
        assert all(lead[k] >= lead[k + 1] for k in range(r - 1))
        c = f[lead]
        res[lead] = c
        f = padd(f, pscale(-c, schur_ssyt(lead, r)))
    return res


# ---------------------------------------------------------------- crystals
def alpha(i, r):
    a = [0] * r
    a[i - 1], a[i] = 1, -1
    return tuple(a)


def pairing(i, w):
    return w[i - 1] - w[i]


def strings(F, b, i):
    E = {v: u for u, v in F[i].items()}
    eps, x = 0, b
    while x in E:
        x, eps = E[x], eps + 1
    phi, x = 0, b
    while x in F[i]:
        x, phi = F[i][x], phi + 1
    return eps, phi


def check_crystal(name, V, F, r, eps=None, phi=None, seminormal=True):
    """V: vertex -> weight; F[i]: partial map f_i (dict); eps/phi: dict (i,b)->int or None
    (= string lengths).  Checks Kashiwara's axioms (and seminormality if requested)."""
    if eps is None:
        eps = {(i, b): strings(F, b, i)[0] for i in F for b in V}
        phi = {(i, b): strings(F, b, i)[1] for i in F for b in V}
    good = True
    for i in F:
        fi = F[i]
        ei = {v: u for u, v in fi.items()}
        good &= len(ei) == len(fi)                          # f_i b = b' <-> e_i b' = b
        for b in V:
            good &= phi[(i, b)] - eps[(i, b)] == pairing(i, V[b])
        for u, v in fi.items():
            good &= tuple(a - c for a, c in zip(V[u], alpha(i, r))) == V[v]
            good &= eps[(i, v)] == eps[(i, u)] + 1 and phi[(i, v)] == phi[(i, u)] - 1
        if seminormal:
            for b in V:
                good &= (eps[(i, b)], phi[(i, b)]) == strings(F, b, i)
    check(good, f"{name}: Kashiwara crystal axioms" + (" + seminormality" if seminormal else ""))
    return good


def character(V, r):
    return dict(Counter(V.values()))


B7_V = {'A': (2, 1, 0), 'B': (1, 2, 0), 'C': (2, 0, 1), 'D': (0, 2, 1),
        'E': (1, 0, 2), 'F': (0, 1, 2), 'Z': (1, 1, 1)}
B7_F = {1: {'A': 'B', 'C': 'Z', 'Z': 'D', 'E': 'F'},
        2: {'A': 'C', 'B': 'Z', 'Z': 'E', 'D': 'F'}}

# B(2,1,0): SSYT 11/2, 12/2, 11/3, 12/3, 13/2, 13/3, 22/3, 23/3
B210_V = {'11/2': (2, 1, 0), '12/2': (1, 2, 0), '11/3': (2, 0, 1), '12/3': (1, 1, 1),
          '13/2': (1, 1, 1), '13/3': (1, 0, 2), '22/3': (0, 2, 1), '23/3': (0, 1, 2)}
B210_F = {1: {'11/2': '12/2', '11/3': '12/3', '12/3': '22/3', '13/3': '23/3'},
          2: {'11/2': '11/3', '12/2': '13/2', '13/2': '13/3', '22/3': '23/3'}}

B100_V = {1: (1, 0, 0), 2: (0, 1, 0), 3: (0, 0, 1)}
B100_F = {1: {1: 2}, 2: {2: 3}}


def word_crystal(n, r):
    """B(1)^{(x) n} for gl_r, Kashiwara tensor rule via the signature rule (letters 1..r)"""
    V = {w: tuple(w.count(k) for k in range(1, r + 1)) for w in product(range(1, r + 1), repeat=n)}
    F = {}
    for i in range(1, r):
        F[i] = {}
        for w in V:
            # signature rule: each letter i+1 is bracketed with the nearest unbracketed letter i
            # to its right; f_i changes the rightmost unbracketed i into i+1 (one of the two
            # standard tensor-product conventions; the checker below re-verifies all axioms).
            stack, free_plus = [], []
            for pos, a in enumerate(w):
                if a == i + 1:
                    stack.append(pos)
                elif a == i:
                    if stack:
                        stack.pop()
                    else:
                        free_plus.append(pos)
            if free_plus:
                p = free_plus[-1]
                F[i][w] = w[:p] + (i + 1,) + w[p + 1:]
    return V, F


# ---------------------------------------------------------------- 1. the crystal
print("== 1. crystal axioms")
check_crystal("B7 (7-vertex)", B7_V, B7_F, 3)
for i in (1, 2):
    for b in sorted(B7_V):
        e, p = strings(B7_F, b, i)
        print(f"      i={i} {b} wt={B7_V[b]} eps={e} phi={p}")
check_crystal("B(1,0,0)", B100_V, B100_F, 3)
check_crystal("B(2,1,0)", B210_V, B210_F, 3)
WV, WF = word_crystal(3, 3)
check_crystal("B(1)^(x)3 (27 words, tensor rule)", WV, WF, 3)
check(len(B7_V) == 7 and len(set(B7_V.values())) == 7, "B7 has 7 vertices with 7 distinct weights")
# connectedness of B7
adj = {b: set() for b in B7_V}
for i in B7_F:
    for u, v in B7_F[i].items():
        adj[u].add(v)
        adj[v].add(u)
seen, todo = {'A'}, ['A']
while todo:
    x = todo.pop()
    for y in adj[x] - seen:
        seen.add(y)
        todo.append(y)
check(seen == set(B7_V), "B7 is connected")
# B7 is obtained from B(2,1,0) by merging 12/3 and 13/2 into Z
ren = {'11/2': 'A', '12/2': 'B', '11/3': 'C', '22/3': 'D', '13/3': 'E', '23/3': 'F',
       '12/3': 'Z', '13/2': 'Z'}
merged = {i: {ren[u]: ren[v] for u, v in B210_F[i].items()} for i in B210_F}
check(merged == B7_F, "B7 = B(2,1,0) with 12/3 and 13/2 identified (all 8 edges kept)")

# ---------------------------------------------------------------- 2. character, Schur
print("== 2. character and Schur polynomials")
r = 3
ch = character(B7_V, r)
check(is_symmetric(ch, r), "ch(B7) is S_3-symmetric")
parts3 = [(3, 0, 0), (2, 1, 0), (1, 1, 1)]
for lam in parts3 + [(1, 0, 0), (2, 0, 0), (1, 1, 0), (3, 1, 0), (2, 2, 0), (2, 1, 1)]:
    check(schur_ssyt(lam, r) == schur_bialt(lam, r),
          f"s_{lam}: SSYT definition = bialternant a_(lam+rho)/a_rho ({sum(schur_ssyt(lam, r).values())} monomials)")
s = {lam: schur_ssyt(lam, r) for lam in parts3}
check(s[(2, 1, 0)] == padd({e: 1 for e in permutations((2, 1, 0))}, {(1, 1, 1): 2}),
      "s_210 = m_210 + 2 m_111")
check(ch == padd(s[(2, 1, 0)], pscale(-1, s[(1, 1, 1)])), "ch(B7) = s_210 - s_111 (polynomial identity)")
# uniqueness: coefficients of x^300, x^210, x^111 in s_300, s_210, s_111 (unitriangular)
M = [[s[lam].get(mu, 0) for lam in parts3] for mu in parts3]
check(M == [[1, 0, 0], [1, 1, 0], [1, 2, 1]], f"coefficient matrix [x^mu] s_lam = {M} is unitriangular")

# ---------------------------------------------------------------- 3. symmetrizations
print("== 3. symmetrization readings")
rh = rho(r)
num = J(pmul(mono(rh), ch), r)
den = J(mono(rh), r)
q = pdiv(num, den)
check(q == ch, "Weyl symmetrizer J(x^rho ch)/J(x^rho) (exact division) = ch")
e1 = schur_expand_bialt(ch, r)
e2 = schur_expand_peel(q, r)
check(e1 == e2 == {(2, 1, 0): 1, (1, 1, 1): -1},
      f"Weyl symmetrization: Schur expansion {e1} (bialternant) = {e2} (SSYT peeling)")
check(num == padd(J(mono((4, 2, 0)), r), pscale(-1, J(mono((3, 2, 1)), r))),
      "J(x^rho ch) = a_(4,2,0) - a_(3,2,1)")
orb = padd(*[act(w, ch) for w in permutations(range(r))])
eo = schur_expand_peel(orb, r)
check(eo == {(2, 1, 0): 6, (1, 1, 1): -6}, f"orbit sum: Schur expansion {eo}")
avg = {e: Fraction(c, 6) for e, c in orb.items()}
ea = schur_expand_peel(avg, r)
check(ea == {(2, 1, 0): 1, (1, 1, 1): -1}, f"orbit average: Schur expansion {ea}")
# Demazure-operator form of the symmetrizer: pi_{w0} = pi_1 pi_2 pi_1
def demazure(i, p):
    out = Counter()
    for e, c in p.items():
        k = e[i - 1] - e[i]
        a = alpha(i, r)
        if k >= 0:
            for j in range(k + 1):
                out[tuple(x - j * y for x, y in zip(e, a))] += c
        elif k <= -2:
            for j in range(1, -k):
                out[tuple(x + j * y for x, y in zip(e, a))] -= c
    return clean(out)
pw0 = demazure(1, demazure(2, demazure(1, ch)))
check(pw0 == ch, "Demazure form pi_1 pi_2 pi_1 (ch) = ch (same Schur expansion, coefficient -1)")
# the normal crystals pass
for name, V in [("B(1,0,0)", B100_V), ("B(2,1,0)", B210_V), ("B(1)^(x)3", WV)]:
    ex = schur_expand_bialt(character(V, r), r)
    check(all(c >= 0 for c in ex.values()), f"{name}: Schur expansion {ex} is nonnegative")

# ---------------------------------------------------------------- 4. classification + minimality
print("== 4. seminormal characters, gl_2 impossibility, gl_3 minimality")


def admissible(ch, r):
    """W-invariant and, for every i and weight nu with <h_i,nu> >= 0: m(nu+alpha_i) <= m(nu)"""
    if not is_symmetric(ch, r):
        return False
    for i in range(1, r):
        a = alpha(i, r)
        for w in ch:
            nu = tuple(x - y for x, y in zip(w, a))   # w = nu + alpha_i
            if pairing(i, nu) >= 0 and ch.get(w, 0) > ch.get(nu, 0):
                return False
    return True


def realize(ch, r):
    """build a seminormal crystal with character ch: per colour, peel symmetric strings"""
    V = {}
    pool = {}
    for w, m in ch.items():
        pool[w] = [f"{w}#{k}" for k in range(m)]
        for v in pool[w]:
            V[v] = w
    F = {}
    for i in range(1, r):
        a = alpha(i, r)
        F[i] = {}
        avail = {w: list(vs) for w, vs in pool.items()}
        for w in sorted(ch, key=lambda w: -pairing(i, w)):
            while pairing(i, w) >= 0 and avail[w]:
                top = avail[w].pop()
                cur, x = top, w
                for _ in range(pairing(i, w)):
                    x = tuple(p - q for p, q in zip(x, a))
                    nxt = avail[x].pop()
                    F[i][cur] = nxt
                    cur = nxt
    return V, F


# gl_2: all admissible characters with <= 10 vertices (degree class mod 2, spread <= 9)
N2 = 10
bad2 = 0
cnt2 = 0
for d in (0, 1):
    doms = [((d + p) // 2, (d - p) // 2) for p in range(0, N2) if (d + p) % 2 == 0]
    def rec2(idx, budget, cur):
        global bad2, cnt2
        if idx == len(doms):
            chh = Counter()
            for lam, m in cur:
                for w in set(permutations(lam)):
                    chh[w] += m
            if chh and admissible(dict(chh), 2):
                cnt2 += 1
                if any(c < 0 for c in schur_expand_bialt(dict(chh), 2).values()):
                    bad2 += 1
            return
        sz = len(set(permutations(doms[idx])))
        for m in range(budget // sz + 1):
            rec2(idx + 1, budget - m * sz, cur + ([(doms[idx], m)] if m else []))
    rec2(0, N2, [])
check(bad2 == 0, f"gl_2: all {cnt2} seminormal characters with <= {N2} vertices are Schur positive")


def search3(N):
    found, total, allc = [], 0, []
    for d in (0, 1, 2):
        doms = []
        for p in range(N):
            for qq in range(N):
                if (d - p - 2 * qq) % 3 == 0:
                    l3 = (d - p - 2 * qq) // 3
                    doms.append((l3 + p + qq, l3 + qq, l3))
        def rec(idx, budget, cur):
            nonlocal total
            if idx == len(doms):
                chh = Counter()
                for lam, m in cur:
                    for w in set(permutations(lam)):
                        chh[w] += m
                chh = dict(chh)
                if chh and admissible(chh, 3):
                    total += 1
                    ex = schur_expand_bialt(chh, 3)
                    allc.append((sum(chh.values()), cur, ex))
                    if any(c < 0 for c in ex.values()):
                        found.append((sum(chh.values()), cur, ex, chh))
                return
            sz = len(set(permutations(doms[idx])))
            for m in range(budget // sz + 1):
                rec(idx + 1, budget - m * sz, cur + ([(doms[idx], m)] if m else []))
        rec(0, N, [])
    return found, total, allc


f6, t6, all6 = search3(6)
check(not f6, f"gl_3: all {t6} seminormal characters with <= 6 vertices (one degree, mod det) are Schur positive:")
for n, cur, ex in sorted(all6):
    print(f"      {n} vertices, dominant weights x mult {cur}, Schur expansion {ex}")
f7, t7, _ = search3(7)
check(len(f7) > 0, f"gl_3: {t7} seminormal characters with <= 7 vertices, {len(f7)} not Schur positive:")
for n, cur, ex, chh in f7:
    print(f"      {n} vertices, dominant weights x mult {cur}, Schur expansion {ex}")
    V, F = realize(chh, 3)
    check_crystal(f"      realisation of {cur}", V, F, 3)
check(admissible(ch, 3), "ch(B7) satisfies the string condition (consistent with step 1)")

# ---------------------------------------------------------------- 5. remark: abstract crystal
print("== 5. remark: 1-vertex abstract (non-seminormal) gl_2 crystal")
V1 = {'b': (-1, 2)}
F1 = {1: {}}
check_crystal("1-vertex crystal wt=(-1,2), eps=3, phi=0", V1, F1, 2,
              eps={(1, 'b'): 3}, phi={(1, 'b'): 0}, seminormal=False)
c1 = character(V1, 2)
check(schur_expand_bialt(c1, 2) == {(1, 0): -1}, f"Weyl symmetrizer: {schur_expand_bialt(c1, 2)}")
orb1 = padd(*[act(w, c1) for w in permutations(range(2))])
check(schur_expand_peel(orb1, 2) == {(2, -1): 1, (1, 0): -1},
      f"orbit sum: {schur_expand_peel(orb1, 2)}")

print("ALL CHECKS PASSED" if OK else "SOME CHECK FAILED")
sys.exit(0 if OK else 1)
