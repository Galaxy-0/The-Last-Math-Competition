#!/usr/bin/env python3
"""Independent check (Python 3 standard library only) for conjecture 00000001753.

Claim refuted: |chi(g)| <= 2^(floor(n/4)-1) for every spin character chi of 2.S_n and every g
lying over an even permutation.  At n = 5 the bound is 1, but the basic spin character
(degree 4) takes the value -2 (resp. 2) on t1*t2, which lies over the 3-cycle (1 2 3).

Parts
  A. The integral model used in Lean (lean4/Main.lean, def T5), exact arithmetic in Z[zeta8]:
     relations of both covers, full enumeration of the group (240 elements), projection to S_5
     with kernel {+-I}, <chi,chi> = 1 (irreducible, a different method from Lean's spanning
     certificate), chi(z) = -4, all character values on even classes.
  B. The Clifford model T_i = (xi_i - xi_{i+1})/sqrt2 for n = 5, exact in Q(zeta8).
  C. The Clifford model for n = 4, 5, 6, 7 in F_p (p = 10^9+9, p = 1 mod 8): group order 2*n!,
     kernel, <chi,chi>, all even-class values, comparison with Schur's formula and the bound.
  D. Other readings: odd classes (n = 4), characters of 2.A_5 (n = 5), exact.
  E. Schur's formula: the lifted 3-cycle beats the bound for every 5 <= n <= 200.
"""
import os, re, math, itertools
from fractions import Fraction as Fr

OK = True
def check(cond, msg):
    global OK
    print(("  ok   " if cond else "  FAIL ") + msg)
    if not cond:
        OK = False

# ---------------------------------------------------------------- Q(zeta8), zeta = e^{i pi/4}
# x = (a, b, c, d) means a + b z + c z^2 + d z^3, z^4 = -1.  Coefficients: int or Fraction.
def zadd(x, y): return (x[0]+y[0], x[1]+y[1], x[2]+y[2], x[3]+y[3])
def zneg(x): return (-x[0], -x[1], -x[2], -x[3])
def zmul(x, y):
    a, b, c, d = x; e, f, g, h = y
    return (a*e - b*h - c*g - d*f, a*f + b*e - c*h - d*g,
            a*g + b*f + c*e - d*h, a*h + b*g + c*f + d*e)
def zconj(x): return (x[0], -x[3], -x[2], -x[1])
ZERO = (0, 0, 0, 0); ONE = (1, 0, 0, 0); I = (0, 0, 1, 0)
SQRT2 = (0, 1, 0, -1)                       # zeta - zeta^3 = sqrt 2
def zscale(q, x): return tuple(q*c for c in x)
def zreal_rational(x):  # x is a rational number?
    return x[1] == 0 and x[2] == 0 and x[3] == 0
def normsq(x): return zmul(x, zconj(x))     # |x|^2, an element of Q(sqrt2)

def mmul(A, B):
    n = len(A); m = len(B[0]); k = len(B)
    out = []
    for i in range(n):
        row = []
        for j in range(m):
            s = ZERO
            for t in range(k):
                if A[i][t] != ZERO and B[t][j] != ZERO:
                    s = zadd(s, zmul(A[i][t], B[t][j]))
            row.append(s)
        out.append(tuple(row))
    return tuple(out)
def ident(d): return tuple(tuple(ONE if i == j else ZERO for j in range(d)) for i in range(d))
def mneg(A): return tuple(tuple(zneg(x) for x in r) for r in A)
def msc(c, A): return tuple(tuple(zmul(c, x) for x in r) for r in A)
def madd(A, B): return tuple(tuple(zadd(x, y) for x, y in zip(r, s)) for r, s in zip(A, B))
def trace(A): 
    s = ZERO
    for i in range(len(A)): s = zadd(s, A[i][i])
    return s
def ev(T, w, d):
    M = ident(d)
    for i in w: M = mmul(M, T[i])
    return M

# ---------------------------------------------------------------- permutations
def swap_adj(p, i):
    p = list(p); p[i], p[i+1] = p[i+1], p[i]; return tuple(p)
def sign(p):
    s = 1
    for i in range(len(p)):
        for j in range(i+1, len(p)):
            if p[i] > p[j]: s = -s
    return s
def cycle_type(p):
    seen = set(); ct = []
    for i in range(len(p)):
        if i in seen: continue
        j = i; l = 0
        while j not in seen:
            seen.add(j); j = p[j]; l += 1
        ct.append(l)
    return tuple(sorted(ct, reverse=True))

def schur_relations(T, d, cover):
    """t_i^2 = e, (t_i t_{i+1})^3 = e, (t_i t_j)^2 = z (|i-j|>=2), with z -> -I and
    e = 1 (hat) or z (tilde)."""
    m = len(T); Id = ident(d); mI = mneg(Id)
    e = Id if cover == 'hat' else mI
    ok = all(ev(T, [i, i], d) == e for i in range(m))
    ok &= all(ev(T, [i, i+1]*3, d) == e for i in range(m-1))
    ok &= all(ev(T, [i, j]*2, d) == mI for i in range(m) for j in range(i+2, m))
    return ok

def enumerate_group(T, d, n):
    """BFS over right multiplication by the generators, tracking the permutation
    t_i -> (i i+1).  Returns dict matrix -> permutation; checks the map is well defined."""
    Id = ident(d); start = tuple(range(n))
    G = {Id: start}; fr = [Id]; consistent = True
    while fr:
        nf = []
        for M in fr:
            for i, t in enumerate(T):
                N = mmul(M, t); q = swap_adj(G[M], i)
                if N in G:
                    consistent &= (G[N] == q)
                else:
                    G[N] = q; nf.append(N)
        fr = nf
    return G, consistent

def char_report(G, d, n, label):
    Id = ident(d)
    order = len(G)
    check(order == 2*math.factorial(n), f"{label}: |G| = {order} = 2*{n}!")
    ker = [M for M, p in G.items() if p == tuple(range(n))]
    check(sorted(ker) == sorted([Id, mneg(Id)]), f"{label}: kernel of G -> S_{n} is {{I, -I}}")
    tot = ZERO
    for M in G: tot = zadd(tot, normsq(trace(M)))
    ip = tuple(Fr(c, order) for c in tot)
    return ip

# ================================================================= Part A: the Lean model
print("Part A. The integral model T5 of lean4/Main.lean (exact, Z[zeta8])")
here = os.path.dirname(os.path.abspath(__file__))
src = open(os.path.join(here, "lean4", "Main.lean"), encoding="utf-8").read()
block = src[src.index("def T5 : List Mat :="):]
block = block[:min(i for i in (block.find("\n\n"), block.find("\n/--"), block.find("\ndef ", 5)) if i > 0)]
nums = re.findall(r"z ((?:\(-?\d+\)|-?\d+) (?:\(-?\d+\)|-?\d+) (?:\(-?\d+\)|-?\d+) (?:\(-?\d+\)|-?\d+))", block)
ents = [tuple(int(t.strip("()")) for t in s.split()) for s in nums]
check(len(ents) == 64, "parsed 4 matrices of size 4x4 from Main.lean")
T5 = [tuple(tuple(ents[16*k + 4*i + j] for j in range(4)) for i in range(4)) for k in range(4)]
T5t = [msc(I, t) for t in T5]
check(schur_relations(T5, 4, 'hat'), "T5 satisfies the relations of hat S_5 (t^2 = 1) with z -> -I")
check(schur_relations(T5t, 4, 'tilde'), "i*T5 satisfies the relations of tilde S_5 (t^2 = z) with z -> -I")
for cover, T in (('hat', T5), ('tilde', T5t)):
    G, cons = enumerate_group(T, 4, 5)
    check(cons, f"{cover}: the permutation of an element does not depend on the word")
    ip = char_report(G, 4, 5, f"Lean model, {cover} S_5")
    check(ip == (1, 0, 0, 0), f"{cover}: <chi,chi> = {ip[0]} (irreducible)")
    check(trace(mneg(ident(4))) == (-4, 0, 0, 0), f"{cover}: chi(z) = -4 = -chi(1) (spin character)")
    vals = {}
    for M, p in G.items():
        if sign(p) == 1:
            vals.setdefault(cycle_type(p), set()).add(trace(M))
    for ct in sorted(vals):
        vs = sorted(v[0] for v in vals[ct]) if all(zreal_rational(v) for v in vals[ct]) else vals[ct]
        print(f"       even class {ct}: chi values {vs}")
    t12 = trace(ev(T, [0, 1], 4))
    p12 = swap_adj(swap_adj(tuple(range(5)), 0), 1)
    print(f"       chi(t1 t2) = {t12[0]}, t1 t2 lies over {p12} (cycle type {cycle_type(p12)}, sign {sign(p12)})")
    check(zreal_rational(t12) and t12[0]**2 == 4 and sign(p12) == 1 and cycle_type(p12) == (3, 1, 1),
          f"{cover}: |chi(t1 t2)|^2 = 4 > 1 = (2^(floor(5/4)-1))^2 at a lift of a 3-cycle")

# ================================================================= Clifford models
def kron(A, B):
    n, m = len(A), len(B)
    return tuple(tuple(zmul(A[i//m][j//m], B[i % m][j % m]) for j in range(n*m)) for i in range(n*m))
PX = ((ZERO, ONE), (ONE, ZERO)); PY = ((ZERO, zneg(I)), (I, ZERO)); PZ = ((ONE, ZERO), (ZERO, zneg(ONE)))
P1 = ident(2)
def clifford(n):
    """n pairwise anticommuting involutions (Jordan-Wigner) of size 2^floor(n/2)."""
    k = n // 2; gens = []
    for a in range(k):
        for P in (PX, PY):
            M = ((ONE,),)
            for b in range(k):
                M = kron(M, PZ if b < a else (P if b == a else P1))
            gens.append(M)
    if n % 2 == 1:
        M = ((ONE,),)
        for b in range(k): M = kron(M, PZ)
        gens.append(M)
    return gens[:n]
HALF_SQRT2 = (Fr(0), Fr(1, 2), Fr(0), Fr(-1, 2))   # 1/sqrt2
def basic_spin(n):
    xi = clifford(n)
    T = [msc(HALF_SQRT2, madd(xi[i], mneg(xi[i+1]))) for i in range(n-1)]
    return xi, T

print("\nPart B. Clifford model for n = 5, exact in Q(zeta8): T_i = (xi_i - xi_{i+1})/sqrt2")
xi5, T = basic_spin(5)
d = len(T[0])
check(all(madd(mmul(xi5[a], xi5[b]), mmul(xi5[b], xi5[a])) == (msc((2, 0, 0, 0), ident(d)) if a == b else msc(ZERO, ident(d)))
          for a in range(5) for b in range(5)), "xi_1..xi_5 are anticommuting involutions (4x4)")
check(schur_relations(T, d, 'hat'), "relations of hat S_5 with z -> -I")
check(schur_relations([msc(I, t) for t in T], d, 'tilde'), "i*T: relations of tilde S_5 with z -> -I")
G5, cons = enumerate_group(T, d, 5)
check(cons, "permutation map well defined")
ip = char_report(G5, d, 5, "Clifford model, n = 5")
check(ip == (1, 0, 0, 0), "<chi,chi> = 1")
t12 = trace(ev(T, [0, 1], d))
check(t12 == (-2, 0, 0, 0), "chi(t1 t2) = -2")

# ---------------------------------------------------------------- F_p model for n = 4..7
P = 10**9 + 9
assert P % 8 == 1
def find_zeta():
    for a in range(2, 1000):
        x = pow(a, (P - 1) // 8, P)
        if pow(x, 4, P) == P - 1:
            return x
ZP = find_zeta()
def tofp(x):   # Q(zeta8) -> F_p, zeta -> ZP (a ring homomorphism; denominators are powers of 2)
    s = 0
    for k, c in enumerate(x):
        c = Fr(c)
        s += c.numerator * pow(c.denominator, P - 2, P) * pow(ZP, k, P)
    return s % P
def fp_group(T, d, n):
    Tp = [[[tofp(T[g][i][j]) for j in range(d)] for i in range(d)] for g in range(len(T))]
    cols = [[[(k, Tp[g][k][j]) for k in range(d) if Tp[g][k][j]] for j in range(d)] for g in range(len(T))]
    Id = tuple(1 if i == j else 0 for i in range(d) for j in range(d))
    G = {Id: tuple(range(n))}; fr = [Id]; cons = True
    while fr:
        nf = []
        for M in fr:
            for g in range(len(T)):
                N = tuple(sum(M[r*d + k]*v for k, v in cols[g][j]) % P for r in range(d) for j in range(d))
                q = swap_adj(G[M], g)
                if N in G: cons &= (G[N] == q)
                else: G[N] = q; nf.append(N)
        fr = nf
    return G, cons
def sym(x): return x - P if x > P // 2 else x
def schur_value(ct):  # |basic spin| on an all-odd-parts class: 2^floor((l-1)/2)
    return 2 ** ((len(ct) - 1) // 2)

print(f"\nPart C. Clifford model in F_p, p = {P} (zeta8 -> {ZP}), n = 4, 5, 6, 7")
for n in (4, 5, 6, 7):
    xi, T = basic_spin(n)
    d = len(T[0])
    check(schur_relations(T, d, 'hat'), f"n = {n}: relations of hat S_{n} hold exactly (degree {d})")
    G, cons = fp_group(T, d, n)
    check(cons and len(G) == 2*math.factorial(n), f"n = {n}: |G| = {len(G)} = 2*{n}!, permutation map well defined")
    ker = [M for M, p in G.items() if p == tuple(range(n))]
    check(len(ker) == 2, f"n = {n}: kernel of G -> S_{n} has 2 elements")
    tr = {M: sym(sum(M[i*d + i] for i in range(d)) % P) for M in G}
    ipn = sum(v*v for v in tr.values())   # traces are rational integers here (real, |.|^2 = v^2)
    expect = 1 if n % 2 == 1 else 2       # n even: sum of the two associate basic spin characters
    check(ipn == expect * len(G), f"n = {n}: <chi,chi> = {Fr(ipn, len(G))} (= {expect})")
    mult = 1 if n % 2 == 1 else 2         # n even: basic spin = chi/2 on even classes
    bound = 2 ** (n // 4 - 1) if n >= 4 else Fr(1, 2)
    worst = 0; agree = True
    for M, p in G.items():
        if sign(p) == 1:
            ct = cycle_type(p)
            v = Fr(tr[M], mult)
            if all(c % 2 == 1 for c in ct):
                agree &= (abs(v) == schur_value(ct))
            else:
                agree &= (v == 0)
            if p != tuple(range(n)):
                worst = max(worst, abs(v))
    check(agree, f"n = {n}: even-class values of the basic spin character agree with Schur's formula")
    v3 = Fr(abs(sym(tofp(trace(ev(T, [0, 1], d))))), mult)
    print(f"       n = {n}: degree {Fr(d, mult)}, bound 2^(floor(n/4)-1) = {bound}, "
          f"|chi(lift of 3-cycle)| = {v3}, max |chi| over even non-identity classes = {worst}")
    if n >= 5:
        check(v3 > bound, f"n = {n}: the lifted 3-cycle violates the bound")
    else:
        check(Fr(d, mult) > bound, f"n = 4: the identity (degree 2) violates the bound (3-cycle value 1 does not)")

# ================================================================= Part D: other readings
print("\nPart D. Other readings")
# odd classes, n = 4: split the 4-dim Clifford module into the two associate basic spin
# representations with the central element w = xi1 xi2 xi3 xi4 (xi1+xi2+xi3+xi4), w^2 = -4.
xi, T = basic_spin(4)
Gam = ev(xi, [0, 1, 2, 3], 4)
s = madd(madd(xi[0], xi[1]), madd(xi[2], xi[3]))
w = mmul(Gam, s)
check(mmul(w, w) == msc((-4, 0, 0, 0), ident(4)), "n = 4: w^2 = -4")
check(all(mmul(w, t) == mmul(t, w) for t in T), "n = 4: w commutes with every T_i")
Pplus = msc((Fr(1, 2), 0, 0, 0), madd(ident(4), msc((0, 0, Fr(-1, 2), 0), w)))   # (1 - (i/2) w)/2
check(mmul(Pplus, Pplus) == Pplus and trace(Pplus) == (2, 0, 0, 0), "n = 4: P = (1 - i w/2)/2 is a rank-2 projector")
g = ev(T, [0, 1, 2], 4)     # t1 t2 t3 lies over a 4-cycle (odd)
p = tuple(range(4))
for i in (0, 1, 2): p = swap_adj(p, i)
v = trace(mmul(g, Pplus))
check(sign(p) == -1 and cycle_type(p) == (4,), f"n = 4: t1 t2 t3 lies over the odd 4-cycle {p}")
print(f"       chi_+(t1 t2 t3) = {tuple(str(c) for c in v)} (a + b zeta + c zeta^2 + d zeta^3; zeta + zeta^3 = i*sqrt2)")
check(normsq(v) == (2, 0, 0, 0), "n = 4, odd-class reading: |chi_+(4-cycle)|^2 = 2 > 1 = bound^2")
# characters of 2.A_5: split the basic spin module of 2.S_5 with s = sum xi_i (s^2 = 5, s commutes
# with the even elements).  psi_+-(g) = (chi(g) +- tr(g s)/sqrt5)/2 on 2.A_5.
xi, T = basic_spin(5)
s = xi[0]
for k in range(1, 5): s = madd(s, xi[k])
check(mmul(s, s) == msc((5, 0, 0, 0), ident(4)), "n = 5: s = xi_1+...+xi_5 has s^2 = 5")
check(all(mmul(s, mmul(T[i], T[j])) == mmul(mmul(T[i], T[j]), s) for i in range(4) for j in range(4)),
      "n = 5: s commutes with all T_i T_j (hence with 2.A_5)")
g = ev(T, [0, 1, 2, 3], 4)  # lies over a 5-cycle
chi = trace(g); t = trace(mmul(g, s))
print(f"       lift of a 5-cycle: chi = {chi[0]}, tr(g s) = {t[0]}; psi = (chi +- tr(gs)/sqrt5)/2")
check(chi == (1, 0, 0, 0) and t in ((5, 0, 0, 0), (-5, 0, 0, 0)),
      "2.A_5 reading: psi = (1 +- sqrt5)/2, and |(1+sqrt5)/2| > 1 (also psi(1) = 2 > 1)")

# ================================================================= Part E: Schur's formula
print("\nPart E. Schur's formula for the basic spin character (n >= 5)")
bad = [n for n in range(5, 201) if not (2 ** ((n - 3) // 2) > 2 ** (n // 4 - 1))]
check(not bad, "for 5 <= n <= 200: 2^floor((n-3)/2) (value at a lifted 3-cycle) > 2^(floor(n/4)-1)")
check(all((n - 3) // 2 > n // 4 - 1 for n in range(5, 10**4)), "exponent inequality floor((n-3)/2) > floor(n/4)-1 for 5 <= n < 10^4 (it holds for all n >= 5)")

print("\nALL CHECKS PASSED" if OK else "\nSOME CHECK FAILED")
raise SystemExit(0 if OK else 1)
