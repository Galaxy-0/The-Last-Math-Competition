#!/usr/bin/env python3
"""Independent check for conjecture 00000001022 (Python 3 standard library only).

Clause refuted: "for any [n,k]_q code, trellis complexity >= min(k, n-k) * ceil(log2 q)".

Methods (different from the Lean proof, which enumerates paths and counts subcodes by filtering):
  1. Codes over GF(p) are built from generator matrices; the minimal (BCJR/Forney) state profile is
     computed from RANKS:  s_i = rank G_[0,i) + rank G_[i,n) - k  (Gaussian elimination mod p),
     and cross-checked against |C| / (|P_i| |F_i|) by counting.
  2. The minimal trellis is also BUILT explicitly as the syndrome (Wolf/BCJR) trellis from a
     parity-check matrix, pruned to the states lying on a root-to-toor path; its layer sizes must
     match the profile and its path-label set must equal the code.
  3. The explicit 1,2,1,2,...,1 trellis is expanded forward layer by layer (sets of (prefix, state))
     and its path labels compared with C; all complexity measures are computed.
  4. The family {00,11}^m (m = 1..8), q-ary analogues (q = 3, 5), all coordinate orders for small
     codes, an exhaustive scan of ALL binary linear codes of length <= 6, and non-vacuity checks.
"""
from itertools import product, permutations
import math

OK = True


def check(cond, msg):
    global OK
    print(("PASS " if cond else "FAIL ") + msg)
    if not cond:
        OK = False


def clog2(q):
    e = 0
    while 2 ** e < q:
        e += 1
    return e


# ------------------------------------------------------------------ linear algebra mod p
def rank_mod(rows, p):
    rows = [list(r) for r in rows if any(r)]
    if not rows:
        return 0
    m = len(rows[0])
    r = 0
    for c in range(m):
        piv = next((i for i in range(r, len(rows)) if rows[i][c] % p), None)
        if piv is None:
            continue
        rows[r], rows[piv] = rows[piv], rows[r]
        inv = pow(rows[r][c], p - 2, p)
        rows[r] = [(x * inv) % p for x in rows[r]]
        for i in range(len(rows)):
            if i != r and rows[i][c] % p:
                f = rows[i][c]
                rows[i] = [(a - f * b) % p for a, b in zip(rows[i], rows[r])]
        r += 1
        if r == len(rows):
            break
    return r


def codewords(G, p):
    n = len(G[0])
    return {tuple(sum(c * g[j] for c, g in zip(cs, G)) % p for j in range(n))
            for cs in product(range(p), repeat=len(G))}


def profile_rank(G, p):
    n, k = len(G[0]), len(G)
    return [rank_mod([g[:i] for g in G], p) + rank_mod([g[i:] for g in G], p) - k
            if 0 < i < n else 0 for i in range(n + 1)]


def profile_count(C, n, p):
    """log_p of |C| / (|P_i| |F_i|), by counting."""
    out = []
    for i in range(n + 1):
        P = sum(1 for c in C if not any(c[i:]))
        F = sum(1 for c in C if not any(c[:i]))
        v = len(C) // (P * F)
        e = round(math.log(v, p))
        assert p ** e == v and len(C) % (P * F) == 0
        out.append(e)
    return out


def parity_check(G, p):
    """Basis of the dual code (null space of G) mod p."""
    n = len(G[0])
    dual = [v for v in product(range(p), repeat=n)
            if all(sum(a * b for a, b in zip(v, g)) % p == 0 for g in G)]
    basis = []
    for v in dual:
        if rank_mod(basis + [list(v)], p) > len(basis):
            basis.append(list(v))
    return basis


def syndrome_trellis(G, p):
    """BCJR/Wolf syndrome trellis, pruned; returns layer sizes, edge counts and path labels."""
    n = len(G[0])
    H = parity_check(G, p)
    r = len(H)
    zero = (0,) * r
    fwd = [{zero}]
    for i in range(n):
        fwd.append({tuple((s[j] + a * H[j][i]) % p for j in range(r)) for s in fwd[-1] for a in range(p)})
    bwd = [None] * (n + 1)
    bwd[n] = {zero}
    for i in range(n - 1, -1, -1):
        bwd[i] = {s for s in fwd[i] for a in range(p)
                  if tuple((s[j] + a * H[j][i]) % p for j in range(r)) in bwd[i + 1]}
    layers = [fwd[i] & bwd[i] for i in range(n + 1)]
    edges = [[(s, a, tuple((s[j] + a * H[j][i]) % p for j in range(r))) for s in layers[i]
              for a in range(p)] for i in range(n)]
    edges = [[e for e in E if e[2] in layers[i + 1]] for i, E in enumerate(edges)]
    cur = {((), zero)}
    for i in range(n):
        cur = {(w + (a,), t) for (w, s) in cur for (s2, a, t) in edges[i] if s2 == s}
    labs = {w for (w, s) in cur if s == zero}
    return [len(L) for L in layers], [len(E) for E in edges], labs


# ------------------------------------------------------------------ the explicit trellis
def rep_gens(m, p=2):
    n = 2 * m
    return [[1 if j in (2 * i, 2 * i + 1) else 0 for j in range(n)] for i in range(m)]


def rep_trellis(m, p=2):
    """Layers 1,p,1,p,...,1: at even times one state; edge labelled a goes to state a, and from
    state a the only edge is labelled a and returns to the single state (for q=2: secA, secB)."""
    sizes, secs = [1], []
    for _ in range(m):
        secs.append([(0, a, a) for a in range(p)])
        sizes.append(p)
        secs.append([(a, a, 0) for a in range(p)])
        sizes.append(1)
    return sizes, secs


def path_labels(sizes, secs):
    cur = {((), 0)}
    for E in secs:
        cur = {(w + (a,), t) for (w, s) in cur for (s2, a, t) in E if s2 == s}
    return {w for (w, s) in cur if s == 0}


def measures(sizes, secs):
    V, E = sum(sizes), sum(len(x) for x in secs)
    return {"max states": max(sizes), "max edges/section": max(len(x) for x in secs),
            "total vertices": V, "total edges": E, "Viterbi ops 2|E|-|V|+1": 2 * E - V + 1}


def wf(sizes, secs):
    return (len(sizes) == len(secs) + 1 and sizes[0] == 1 and sizes[-1] == 1 and
            all(0 <= s < sizes[i] and 0 <= t < sizes[i + 1] for i, E in enumerate(secs)
                for (s, a, t) in E) and all(len(set(E)) == len(E) for E in secs))


print("== 1. The [10,5] counterexample C = {00,11}^5")
G10 = rep_gens(5)
C10 = codewords(G10, 2)
n, k = 10, 5
B = min(k, n - k) * clog2(2)
check(len(C10) == 32 and rank_mod(G10, 2) == 5, "C is a binary [10,5] code (32 codewords, rank 5)")
check(B == 5, "claimed bound min(k,n-k)*ceil(log2 q) = 5")
sizes, secs = rep_trellis(5)
check(wf(sizes, secs), "explicit trellis is well formed, layer sizes %s" % sizes)
check(path_labels(sizes, secs) == C10, "explicit trellis: set of path labels == C (layer-by-layer expansion)")
M = measures(sizes, secs)
for name, v in M.items():
    check(math.log2(v) < B, "%s = %d, log2 = %.3f < %d" % (name, v, math.log2(v), B))
check(M == {"max states": 2, "max edges/section": 2, "total vertices": 16, "total edges": 20,
            "Viterbi ops 2|E|-|V|+1": 25}, "measures are 2, 2, 16, 20, 25")
pr = profile_rank(G10, 2)
check(pr == [0, 1] * 5 + [0], "BCJR profile from ranks s_i = rk G_past + rk G_future - k: %s" % pr)
check(profile_count(C10, 10, 2) == pr, "BCJR profile by counting |C|/(|P_i||F_i|) agrees")
ls, es, labs = syndrome_trellis(G10, 2)
check(ls == [2 ** s for s in pr] and labs == C10,
      "syndrome (BCJR) trellis built from H: layer sizes %s, edges/section %s, labels == C" % (ls, es))
check(max(pr) == 1 < B, "minimal trellis: s_max = 1 < 5 (edge complexity log2 max|E_i| = %d < 5)"
      % int(math.log2(max(es))))

print("\n== 2. The smallest instance [4,2]: {0000,1100,0011,1111}")
G4 = rep_gens(2)
C4 = codewords(G4, 2)
check(sorted(C4) == [(0, 0, 0, 0), (0, 0, 1, 1), (1, 1, 0, 0), (1, 1, 1, 1)], "codewords")
check(profile_rank(G4, 2) == [0, 1, 0, 1, 0], "profile 0,1,0,1,0: s_max = 1 < 2 = min(2,2)")
GI = [[1, 0, 1, 0], [0, 1, 0, 1]]
check(profile_rank(GI, 2) == [0, 1, 2, 1, 0],
      "non-vacuity: interleaved order {0000,1010,0101,1111} has profile 0,1,2,1,0 (attains the bound)")
best = min(max(profile_rank([[g[j] for j in pi] for g in G4], 2)) for pi in permutations(range(4)))
worst = max(max(profile_rank([[g[j] for j in pi] for g in G4], 2)) for pi in permutations(range(4)))
check(best == 1 and worst == 2, "over all 24 coordinate orders of this code: min s_max = 1, max s_max = 2")

print("\n== 3. The family {00,11}^m, [2m, m]_2, bound m")
for m in range(1, 9):
    G = rep_gens(m)
    C = codewords(G, 2)
    sz, sc = rep_trellis(m)
    pr = profile_rank(G, 2)
    ok = (len(C) == 2 ** m and wf(sz, sc) and path_labels(sz, sc) == C and max(pr) == 1)
    Mm = measures(sz, sc)
    ok = ok and Mm == {"max states": 2, "max edges/section": 2, "total vertices": 3 * m + 1,
                       "total edges": 4 * m, "Viterbi ops 2|E|-|V|+1": 5 * m}
    below = [nm for nm, v in Mm.items() if v < 2 ** m]
    check(ok, "m=%d: trellis represents C, s_max=1, bound %d; measures below 2^m: %s"
          % (m, m, ", ".join(below) if below else "none"))
check(all(5 * m < 2 ** m for m in range(5, 200)), "5m < 2^m for 5 <= m < 200 (all measures fail for m >= 5)")

print("\n== 4. q-ary analogues: {aa : a in GF(q)}^m, bound m*ceil(log2 q)")
for p in (3, 5):
    for m in range(1, 4 if p == 3 else 3):
        G = rep_gens(m, p)
        C = codewords(G, p)
        sz, sc = rep_trellis(m, p)
        pr = profile_rank(G, p)
        smax_bits = max(pr) * math.log2(p)
        Bq = m * clog2(p)
        check(path_labels(sz, sc) == C and max(sz) == p and max(pr) == 1 and
              (m < 2 or math.ceil(smax_bits) < Bq),
              "q=%d m=%d: [%d,%d]_%d, s_max = log2 %d = %.3f bits, bound %d%s"
              % (p, m, 2 * m, m, p, p, smax_bits, Bq, " (violated)" if smax_bits < Bq else ""))

print("\n== 5. Worst coordinate order: [4,2] code generated by 1000, 0111")
GW = [[1, 0, 0, 0], [0, 1, 1, 1]]
vals = {max(profile_rank([[g[j] for j in pi] for g in GW], 2)) for pi in permutations(range(4))}
check(vals == {1}, "every one of the 24 orders gives s_max = 1 < 2 = min(2,2)")

print("\n== 6. Exhaustive: all binary linear codes of length n <= 6")


def all_subspaces(n):
    vecs = [v for v in range(1, 2 ** n)]
    seen = {frozenset([0])}
    frontier = [frozenset([0])]
    while frontier:
        new = []
        for S in frontier:
            for v in vecs:
                if v not in S:
                    T = frozenset(S | {x ^ v for x in S})
                    if T not in seen:
                        seen.add(T)
                        new.append(T)
        frontier = new
    return seen


for n in range(1, 7):
    subs = all_subspaces(n)
    viol = 0
    wolf_ok = True
    for S in subs:
        k = int(math.log2(len(S)))
        words = [tuple((x >> (n - 1 - j)) & 1 for j in range(n)) for x in S]
        prof = profile_count(set(words), n, 2)
        wolf_ok &= max(prof) <= min(k, n - k)
        viol += max(prof) < min(k, n - k)
    check(wolf_ok, "n=%d: %d codes; Wolf's UPPER bound s_max <= min(k,n-k) holds for all; "
          "%d codes violate the claimed LOWER bound" % (n, len(subs), viol))

print("\n== 7. Non-vacuity: {00,11} needs 2 states in every trellis")
# a trellis with a single middle state: section edges are subsets of {(0,0,0),(0,1,0)}
single = [set(c) for c in [[], [(0, 0, 0)], [(0, 1, 0)], [(0, 0, 0), (0, 1, 0)]]]
reps = [(a, b) for a in single for b in single
        if path_labels([1, 1, 1], [sorted(a), sorted(b)]) == {(0, 0), (1, 1)}]
check(reps == [], "no trellis with one middle state represents {00,11}; so the bound (2 states) holds")

print("\nALL CHECKS PASSED" if OK else "\nSOME CHECK FAILED")
raise SystemExit(0 if OK else 1)
