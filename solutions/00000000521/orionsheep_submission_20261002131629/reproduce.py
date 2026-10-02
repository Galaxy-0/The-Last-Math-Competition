#!/usr/bin/env python3
"""
TLMC conjecture 00000000521 (v2) - recomputation for the LITERAL object:
the graded Betti numbers OF THE IDEAL I as a graded R-module,
beta_{i,j}(I) = dim_k Tor_i^R(I, k).

Conjecture (verbatim object): A_j = sum_i (-1)^i beta_{i,j}(I); for every
edge ideal the sign of {A_j} changes exactly once as j crosses reg(I), and
|A_j| is monotonically nondecreasing up to that point.

v1 error (fixed): v1 used the Betti table of R/I (extra beta_{0,0} = 1).
Here everything is computed for the module I and cross-checked four ways:
  (1) beta^I_{i,j} = dim_k H_i(Taylor(I) (x) k): homology of the Taylor
      resolution OF THE MODULE I tensored with k = GF(10^9+7).  Tor is
      computable from any free resolution; after tensoring with k only the
      constant entries of the Taylor differentials survive, and the ranks
      are computed over GF(P) on 0/+1/-1 matrices, so the result is exact
      (Betti numbers of monomial ideals are field-independent).
  (2) Hilbert cross-check: A_j = [t^j] (1-t)^n * Hilb_I(t), Hilb_I counted
      by direct monomial enumeration (divisibility by a generator).
  (3) Long-exact-sequence identity: A_j(I) = delta_{j0} - A_j(R/I)
      (because beta^I_{i,j} = beta^{R/I}_{i+1,j} for i >= 1 and, for edge
      ideals, beta^I_{0,j} = beta^{R/I}_{1,j}).
  (4) For the flagship counterexample C4, the hand-written minimal free
      resolution 0 -> R(-4) -> R(-3)^4 -> R(-2)^4 -> I -> 0 is verified
      EXPLICITLY: d1 d2 = 0, per-bidegree homology H_1 = H_2 = 0 over GF(P),
      coker(d1) matches Hilb_I degree by degree, all entries of positive
      degree (minimality).

Flagship counterexample: C4, I = (x1x2, x2x3, x3x4, x4x1) in k[x1..x4]:
    beta^I_{0,2} = 4, beta^I_{1,3} = 4, beta^I_{2,4} = 1, reg(I) = 2,
    A = (0, 0, 4, -4, 1):  signs +, -, +  ->  TWO sign changes
    (the conjecture demands exactly one);  the monotonicity clause holds.

Standard library only.  python3 reproduce.py   (exit code 0 = all OK)
"""

from itertools import combinations
from math import comb
import sys

P = 1_000_000_007


# ---------------- linear algebra over GF(P) ----------------

def rank(rows, ncols):
    """Rank of a matrix given as a list of rows of ints, mod P."""
    M = [r[:] for r in rows]
    rk = 0
    for col in range(ncols):
        piv = None
        for i in range(rk, len(M)):
            if M[i][col] % P:
                piv = i
                break
        if piv is None:
            continue
        M[rk], M[piv] = M[piv], M[rk]
        inv = pow(M[rk][col], P - 2, P)
        M[rk] = [(v * inv) % P for v in M[rk]]
        for i in range(len(M)):
            if i != rk and M[i][col] % P:
                f = M[i][col]
                M[i] = [(M[i][j] - f * M[rk][j]) % P for j in range(ncols)]
        rk += 1
    return rk


def bits(mask):
    i, out = 0, []
    while mask:
        if mask & 1:
            out.append(i)
        mask >>= 1
        i += 1
    return out


# ---------- beta^I via the Taylor resolution of the MODULE I ----------

def betti_table_module(gens):
    """
    gens: exponent tuples = minimal monomial generators of I.
    Taylor resolution of the module I:
        F_0 = (+)_g R(-deg g)            (singletons)
        F_i = (+)_{|S|=i+1} R(-lcm(S))   (i >= 1)
    Returns (dims, maxdeg), dims[(i, j)] = beta^I_{i,j}.
    """
    nvars = len(gens[0])
    r = len(gens)
    deg = {}
    for mask in range(1, 1 << r):              # NONEMPTY subsets
        d = (0,) * nvars
        for s in bits(mask):
            d = tuple(max(x, y) for x, y in zip(d, gens[s]))
        deg[mask] = (sum(d), d)
    maxdeg = max(d for (d, _) in deg.values())

    groups = {}
    for mask, (dj, dv) in deg.items():
        groups.setdefault((bin(mask).count("1") - 1, dj), []).append(mask)

    rank_d = {}
    for (i, j), src in groups.items():
        if i == 0:
            rank_d[(i, j)] = 0                 # d_0 = 0
            continue
        tgt = groups.get((i - 1, j), [])
        tcol = {m: c for c, m in enumerate(tgt)}
        rows = []
        for S in src:
            row = [0] * len(tgt)
            for pos, s in enumerate(bits(S)):
                S2 = S & ~(1 << s)
                if deg[S][1] == deg[S2][1]:    # constant entry survives (x)k
                    row[tcol[S2]] = 1 if pos % 2 == 0 else P - 1
            rows.append(row)
        rank_d[(i, j)] = rank(rows, len(tgt)) if rows else 0

    dims = {}
    for (i, j), src in groups.items():
        ker = len(src) - rank_d.get((i, j), 0)
        im_next = rank_d.get((i + 1, j), 0)
        dims[(i, j)] = ker - im_next
    for i in range(r):
        for j in range(maxdeg + 1):
            dims.setdefault((i, j), 0)
    return dims, maxdeg


def betti_table_RI(gens):
    """beta^{R/I} (v1's object): Taylor of R -> R/I (empty set = R summand)."""
    nvars = len(gens[0])
    r = len(gens)
    deg = {}
    for mask in range(1 << r):
        d = (0,) * nvars
        for s in bits(mask):
            d = tuple(max(x, y) for x, y in zip(d, gens[s]))
        deg[mask] = (sum(d), d)
    maxdeg = max(d for (d, _) in deg.values())
    groups = {}
    for mask, (dj, dv) in deg.items():
        groups.setdefault((bin(mask).count("1"), dj), []).append(mask)
    rank_d = {}
    for (i, j), src in groups.items():
        tgt = groups.get((i - 1, j), []) if i > 0 else []
        tcol = {m: c for c, m in enumerate(tgt)}
        rows = []
        for S in src:
            row = [0] * len(tgt)
            for pos, s in enumerate(bits(S)):
                S2 = S & ~(1 << s)
                if deg[S][1] == deg[S2][1]:
                    row[tcol[S2]] = 1 if pos % 2 == 0 else P - 1
            rows.append(row)
        rank_d[(i, j)] = rank(rows, len(tgt)) if rows else 0
    dims = {}
    for (i, j), src in groups.items():
        dims[(i, j)] = len(src) - rank_d.get((i, j), 0) - rank_d.get((i + 1, j), 0)
    for i in range(r + 1):
        for j in range(maxdeg + 1):
            dims.setdefault((i, j), 0)
    return dims, maxdeg


# ---------- Hilbert series of I by direct monomial enumeration ----------

def hilbert_kpoly_I(gens, nvars, D):
    """
    c_j = [t^j] (1-t)^n * Hilb_I(t), j = 0..D.
    Hilb_I(d) = # degree-d monomials divisible by at least one generator.
    """
    h = [0] * (D + 1)
    exp = [0] * nvars

    def divisible():
        return any(all(exp[i] >= g[i] for i in range(nvars)) for g in gens)

    def rec(v, total):
        if v == nvars:
            if divisible():
                h[total] += 1
            return
        for e in range(D - total + 1):
            exp[v] = e
            rec(v + 1, total + e)
        exp[v] = 0

    rec(0, 0)
    return [sum(h[d] * ((-1) ** (j - d)) * comb(nvars, j - d)
                for d in range(j + 1)) for j in range(D + 1)]


# ---------- explicit minimal resolution of the module I(C4) ----------

def check_explicit_resolution_C4():
    """
    I = (x1x2, x2x3, x3x4, x4x1) in k[x1,x2,x3,x4].
    Minimal free resolution OF THE MODULE I:
        0 -> R(-4) --d2-> R(-3)^4 --d1-> R(-2)^4 -> I -> 0
    d1 columns (adjacent-edge syzygies on the generators):
        s12 = ( x3, -x1,  0,  0),  s23 = ( 0,  x4, -x2,  0),
        s34 = ( 0,   0,  x1, -x3),  s41 = ( x4,  0,  0, -x2)
    d2 column (the relation among them, all entries of degree 1):
        rho = (x4, x1, x2, -x3):  x4 s12 + x1 s23 + x2 s34 - x3 s41 = 0.
    Verified over GF(P): d1 d2 = 0; per-bidegree H_1 = H_2 = 0 (exact);
    coker(d1) = Hilb_I per degree; minimality (all entries of degree 1).
    Returns (ok, betti) with betti the Betti numbers of the module I.
    """
    n = 4
    x1 = (1, 0, 0, 0); x2 = (0, 1, 0, 0); x3 = (0, 0, 1, 0); x4 = (0, 0, 0, 1)
    gens = [(1, 1, 0, 0), (0, 1, 1, 0), (0, 0, 1, 1), (1, 0, 0, 1)]

    d1cols = [
        [(0, x3, 1), (1, x1, P - 1)],            # s12
        [(1, x4, 1), (2, x2, P - 1)],            # s23
        [(2, x1, 1), (3, x3, P - 1)],            # s34
        [(0, x4, 1), (3, x2, P - 1)],            # s41
    ]
    rho = [(0, x4, 1), (1, x1, 1), (2, x2, 1), (3, x3, P - 1)]

    # d1 d2 = 0 (polynomial multiplication, sparse monomial vectors)
    prod = [dict() for _ in range(4)]
    for (comp, m, c) in rho:
        for (comp2, m2, c2) in d1cols[comp]:
            key = (comp2, tuple(a + b for a, b in zip(m, m2)))
            prod[key[0]][key[1]] = (prod[key[0]].get(key[1], 0) + c * c2) % P
    d1d2_zero = all(v == 0 for pd in prod for v in pd.values())

    def monos(deg):
        if deg < 0:
            return []
        out = []

        def rec(v, left, cur):
            if v == n:
                out.append(tuple(cur))
                return
            for e in range(left + 1):
                rec(v + 1, left - e, cur + [e])

        rec(0, deg, [])
        return out

    def hilb_I(d):
        cnt = 0
        exp = [0] * n

        def rec(v, left):
            nonlocal cnt
            if v == n:
                if any(all(exp[i] >= g[i] for i in range(n)) for g in gens):
                    cnt += 1
                return
            for e in range(left + 1):
                exp[v] = e
                rec(v + 1, left - e)
            exp[v] = 0

        rec(0, d)
        return cnt

    hom_ok, coker_ok = True, True
    for j in range(0, 8):
        src1 = [(ci, m) for ci in range(4) for m in monos(j - 3)]
        tgt1 = [(ci, m) for ci in range(4) for m in monos(j - 2)]
        src2 = monos(j - 4)
        tcol1 = {t: i for i, t in enumerate(tgt1)}
        tcol2 = {t: i for i, t in enumerate(src1)}
        rows1 = []
        for (ci, m) in src1:
            row = [0] * len(tgt1)
            for (pos, m2, c2) in d1cols[ci]:
                key = (pos, tuple(a + b for a, b in zip(m, m2)))
                if key in tcol1:
                    row[tcol1[key]] = (row[tcol1[key]] + c2) % P
            rows1.append(row)
        rows2 = []
        for m in src2:
            row = [0] * len(src1)
            for (pos, m2, c2) in rho:
                key = (pos, tuple(a + b for a, b in zip(m, m2)))
                if key in tcol2:
                    row[tcol2[key]] = (row[tcol2[key]] + c2) % P
            rows2.append(row)
        r1 = rank(rows1, len(tgt1)) if (rows1 and tgt1) else 0
        r2 = rank(rows2, len(src1)) if (rows2 and src1) else 0
        if len(src2) - r2 != 0:                     # H_2 = ker d2
            hom_ok = False
        if (len(src1) - r1) - r2 != 0:              # H_1 = ker d1 / im d2
            hom_ok = False
        if j >= 2 and (len(tgt1) - r1) - hilb_I(j) != 0:   # coker = Hilb_I
            coker_ok = False

    def deg(m):
        return sum(m)

    minimal = all(deg(m2) >= 1 for col in d1cols for (_, m2, _) in col) and \
        all(deg(m2) >= 1 for (_, m2, _) in rho)

    betti = {(0, 2): 4, (1, 3): 4, (2, 4): 1}
    return d1d2_zero and hom_ok and coker_ok and minimal, betti


# ---------------- analysis under the literal reading ----------------

def sign_changes(seq):
    nz = [x for x in seq if x != 0]
    return sum(1 for a, b in zip(nz, nz[1:]) if (a > 0) != (b > 0))


def nondecreasing(seq):
    return all(a <= b for a, b in zip(seq, seq[1:]))


def analyze(gens, nvars):
    dims, maxdeg = betti_table_module(gens)
    pdI = max(i for (i, j), d in dims.items() if d)
    A = [sum(((-1) ** i) * dims.get((i, j), 0) for i in range(pdI + 1))
         for j in range(maxdeg + 2)]
    regI = max(((j - i) for (i, j), d in dims.items() if d), default=0)

    c = hilbert_kpoly_I(gens, nvars, maxdeg + 2)
    hilbert_ok = (all(A[j] == c[j] for j in range(min(len(A), len(c))))
                  and all(v == 0 for v in c[len(A):]))

    dimsRI, _ = betti_table_RI(gens)
    pdRI = max(i for (i, j), d in dimsRI.items() if d)
    ARI = [sum(((-1) ** i) * dimsRI.get((i, j), 0) for i in range(pdRI + 1))
           for j in range(maxdeg + 2)]
    ident_ok = all(A[j] == (1 if j == 0 else 0) - ARI[j] for j in range(len(A)))

    # beta^I_{0,2} must equal the number of degree-2 generators (edges)
    assert dims.get((0, 2), 0) == sum(1 for g in gens if sum(g) == 2)
    # minimality sanity: I is generated in degree 2, so beta^I_{0,0} = 0
    assert dims.get((0, 0), 0) == 0

    upto = range(min(regI, len(A) - 1) + 1)
    return {
        "dims": dims, "A": A, "regI": regI,
        "hilbert_ok": hilbert_ok, "ident_ok": ident_ok,
        "changes": sign_changes(A),
        "mono_all": nondecreasing([abs(A[j]) for j in upto]),
        "mono_nz": nondecreasing([abs(A[j]) for j in upto if A[j] != 0]),
        "A_RI": ARI, "changes_RI": sign_changes(ARI),
    }


def edge_ideal(nvars, edges):
    gens = []
    for (a, b) in edges:
        t = [0] * nvars
        t[a] = 1
        t[b] = 1
        gens.append(tuple(t))
    return gens


def main():
    print("=" * 78)
    print("TLMC 00000000521 (v2): literal reading, Betti numbers of the ideal I")
    print("=" * 78)

    print("\n[0] Explicit minimal-resolution check for C4:")
    ok, bexp = check_explicit_resolution_C4()
    print(f"    exact + minimal: 0 -> R(-4) -> R(-3)^4 -> R(-2)^4 -> I -> 0 : {ok}")
    print(f"    Betti numbers of the module I: {bexp}")
    assert ok

    print("\n[1] Flagship counterexample C4: I = (x1x2, x2x3, x3x4, x4x1):")
    r = analyze(edge_ideal(4, [(0, 1), (1, 2), (2, 3), (0, 3)]), 4)
    assert r["hilbert_ok"] and r["ident_ok"]
    print("    beta^I_(i,j) != 0 : " +
          ", ".join(f"({i},{j}):{d}" for (i, j), d in sorted(r["dims"].items()) if d))
    print(f"    A = {r['A']},  reg(I) = {r['regI']},  sign changes = {r['changes']}")
    print(f"    (v1 object: A(R/I) = {r['A_RI']}, changes = {r['changes_RI']})")
    print(f"    |A_j| for j <= reg(I): {[abs(r['A'][j]) for j in range(r['regI'] + 1)]}"
          f"  -> monotonicity clause holds: {r['mono_all']}")
    assert r["A"][:5] == [0, 0, 4, -4, 1], r["A"]
    assert r["regI"] == 2 and r["changes"] == 2 and r["mono_all"]
    print("    -> 'exactly once' clause VIOLATED (two changes),")
    print("       while the change at reg(I) = 2 does occur (+4 -> -4).")

    print("\n[2] Reviewer's observation confirmed - C3 holds literally:")
    r = analyze(edge_ideal(3, [(0, 1), (1, 2), (0, 2)]), 3)
    assert r["hilbert_ok"] and r["ident_ok"]
    print(f"    A = {r['A']},  reg(I) = {r['regI']},  changes = {r['changes']}  (holds)")
    assert r["A"][:4] == [0, 0, 3, -2] and r["changes"] == 1

    print("\n[3] Named examples (literal reading, Betti numbers of the module I):")
    named = [
        ("single edge K2",  2, [(0, 1)]),
        ("P3 (2 adj edges)", 3, [(0, 1), (1, 2)]),
        ("2K2",             4, [(0, 1), (2, 3)]),
        ("P4",              4, [(0, 1), (1, 2), (2, 3)]),
        ("star K1,3",       4, [(0, 1), (0, 2), (0, 3)]),
        ("C3",              3, [(0, 1), (1, 2), (0, 2)]),
        ("C4",              4, [(0, 1), (1, 2), (2, 3), (0, 3)]),
        ("paw",             4, [(0, 1), (0, 2), (1, 2), (2, 3)]),
        ("diamond",         4, [(0, 1), (0, 2), (0, 3), (1, 2), (2, 3)]),
        ("K4",              4, [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]),
        ("C5",              5, [(0, 1), (1, 2), (2, 3), (3, 4), (0, 4)]),
        ("C6",              6, [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (0, 5)]),
        ("P3 u K2",         5, [(0, 1), (1, 2), (3, 4)]),
    ]
    for label, nv, es in named:
        r = analyze(edge_ideal(nv, es), nv)
        assert r["hilbert_ok"], f"Hilbert cross-check failed: {label}"
        assert r["ident_ok"], f"LES identity failed: {label}"
        verdict = "VIOLATES exactly-once" if r["changes"] != 1 else "ok"
        print(f"  {label:16s} A(I)={str(r['A']):26s} reg={r['regI']} "
              f"changes={r['changes']}  [{verdict}]")
    print("  (P3 u K2 also violates |A_j| nondecreasing: |A_2|=3 > |A_3|=1, reg=3)")

    print("\n[4] Exhaustive scans (literal reading):")
    for nvars in (4, 5):
        pairs = list(combinations(range(nvars), 2))
        total = v_c1 = v_c2 = v_both = 0
        ex = []
        for mask in range(1, 1 << len(pairs)):
            es = [pairs[k] for k in range(len(pairs)) if mask >> k & 1]
            total += 1
            r = analyze(edge_ideal(nvars, es), nvars)
            bad1 = r["changes"] != 1
            bad2 = not r["mono_nz"]
            if bad1:
                v_c1 += 1
                if len(ex) < 3:
                    ex.append((es, r["A"], r["changes"], r["regI"]))
            if bad2:
                v_c2 += 1
            if bad1 and bad2:
                v_both += 1
        print(f"  graphs on {nvars} vertices with >= 1 edge: {total}")
        print(f"    violate 'exactly one sign change'      : {v_c1}")
        print(f"    violate |A| nondecreasing (zeros skip) : {v_c2}"
              f"   (of which also violate changes-clause: {v_both})")
        for es, A, ch, reg in ex:
            print(f"      e.g. {es}: A = {A}, reg = {reg}, changes = {ch}")

    print("\nAll recomputations and cross-checks PASSED.")
    print("Conclusion: under the literal beta_{i,j}(I) definition the conjecture")
    print("is FALSE: C4 gives A = (0, 0, 4, -4, 1), reg(I) = 2, TWO sign changes.")
    sys.exit(0)


if __name__ == "__main__":
    main()
