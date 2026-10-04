#!/usr/bin/env python3
"""Independent check for conjecture 00000008556 (Python 3 standard library only).

Representation (different from the Lean bitmasks): an element of the free distributive lattice
FD(n) is a monotone Boolean function, stored as the frozenset of its true points, each point a
frozenset of variable indices.  Meet = intersection, join = union.

Checks
  1. FD(n) = closure of the projections under meet/join = nonconstant monotone functions
     (sizes 1, 4, 18, 166; bounded version 3, 6, 20, 168), n = 1..4.
  2. Aut(FD(n)) computed WITHOUT assuming anything:
       n <= 3: brute-force backtracking over all lattice order-automorphisms;
       n = 4 : automorphisms of the poset of join-irreducibles (Birkhoff), by backtracking.
     Result: |Aut| = n! and every automorphism is a permutation of variables (clause 1 holds).
  3. The fixed points of the full Aut group are the threshold functions; they form a chain of
     length n-1 (free) / n+1 (bounded).
  4. p(n) by Euler's pentagonal recurrence, cross-checked against a direct enumeration.
  5. The logarithm clause fails for every base: n=2 forces b = 2 (or b^L = 2), n=3 needs b^L' = 3;
     2^a = 3^c only for a = c = 0.  Also rounding readings and single-automorphism readings.
"""
from itertools import permutations, combinations
import math
import sys

OK = True


def check(cond, msg):
    global OK
    print(("PASS " if cond else "FAIL ") + msg)
    if not cond:
        OK = False


# ---------------------------------------------------------------- lattices
def points(n):
    return [frozenset(c) for k in range(n + 1) for c in combinations(range(n), k)]


def closure(n, bounded):
    pts = points(n)
    gens = {frozenset(x for x in pts if i in x) for i in range(n)}
    if bounded:
        gens |= {frozenset(), frozenset(pts)}
    S = set(gens)
    frontier = set(gens)
    while frontier:
        new = set()
        for a in frontier:
            for b in S | frontier:
                for c in (a & b, a | b):
                    if c not in S:
                        new.add(c)
        S |= new
        frontier = new
    return S


def monotone_functions(n, bounded):
    pts = points(n)
    res = set()
    for mask in range(1 << len(pts)):
        up = frozenset(pts[i] for i in range(len(pts)) if mask >> i & 1)
        if all((y in up) for x in up for y in pts if x <= y):
            if bounded or (0 < len(up) < len(pts)):
                res.add(up)
    return res


def leq(a, b):
    return a <= b


def rank_function(elems):
    """height of each element = length of the longest chain from the bottom."""
    order = sorted(elems, key=len)
    h = {}
    for e in order:
        h[e] = max([h[d] + 1 for d in order if d < e and d in h] + [0])
    return h


def lattice_automorphisms(elems):
    """All order-automorphisms of a finite lattice (brute-force backtracking)."""
    elems = sorted(elems, key=lambda e: (len(e), sorted(map(sorted, e))))
    h = rank_function(elems)
    down = {e: sum(1 for d in elems if d < e) for e in elems}
    up = {e: sum(1 for d in elems if e < d) for e in elems}
    sig = {e: (h[e], down[e], up[e]) for e in elems}
    autos = []
    phi = {}
    used = set()

    def bt(i):
        if i == len(elems):
            autos.append(dict(phi))
            return
        a = elems[i]
        for c in elems:
            if c in used or sig[c] != sig[a]:
                continue
            good = True
            for b, d in phi.items():
                if (b <= a) != (d <= c) or (a <= b) != (c <= d):
                    good = False
                    break
            if good:
                phi[a] = c
                used.add(c)
                bt(i + 1)
                del phi[a]
                used.discard(c)

    bt(0)
    return autos


def join_irreducibles(elems):
    res = []
    for e in elems:
        lower = [d for d in elems if d < e]
        if not lower:
            continue  # bottom
        maxl = [d for d in lower if not any(d < x for x in lower)]
        if len(maxl) == 1:
            res.append(e)
    return res


def poset_automorphisms(P):
    P = list(P)
    autos = []
    phi = {}
    used = set()
    sig = {e: (sum(1 for d in P if d < e), sum(1 for d in P if e < d)) for e in P}

    def bt(i):
        if i == len(P):
            autos.append(dict(phi))
            return
        a = P[i]
        for c in P:
            if c in used or sig[c] != sig[a]:
                continue
            if all(((b <= a) == (d <= c)) and ((a <= b) == (c <= d)) for b, d in phi.items()):
                phi[a] = c
                used.add(c)
                bt(i + 1)
                del phi[a]
                used.discard(c)

    bt(0)
    return autos


def act(sigma, f):
    return frozenset(frozenset(sigma[i] for i in x) for x in f)


def threshold(n, k):
    return frozenset(x for x in points(n) if len(x) >= k)


def longest_chain(S):
    order = sorted(S, key=len)
    best = {}
    for e in order:
        best[e] = max([best[d] + 1 for d in order if d < e and d in best] + [0])
    return max(best.values())  # number of covering steps (edges)


# ---------------------------------------------------------------- partitions
def partitions_pentagonal(N):
    p = [1] + [0] * N
    for m in range(1, N + 1):
        s, k = 0, 1
        while True:
            g1 = k * (3 * k - 1) // 2
            g2 = k * (3 * k + 1) // 2
            if g1 > m:
                break
            sgn = 1 if k % 2 else -1
            s += sgn * p[m - g1]
            if g2 <= m:
                s += sgn * p[m - g2]
            k += 1
        p[m] = s
    return p


def partitions_direct(m, mx=None):
    if mx is None:
        mx = m
    if m == 0:
        return 1
    return sum(partitions_direct(m - a, a) for a in range(1, min(m, mx) + 1))


def main():
    P = partitions_pentagonal(60)
    check(all(P[m] == partitions_direct(m) for m in range(0, 21)),
          "p(n) by pentagonal recurrence agrees with direct enumeration for n <= 20")
    check(P[1:6] == [1, 2, 3, 5, 7], "p(1..5) = 1, 2, 3, 5, 7")

    lengths = {}
    sizes = {False: [1, 4, 18, 166], True: [3, 6, 20, 168]}
    for bounded in (False, True):
        tag = "bounded" if bounded else "free"
        for n in range(1, 5):
            S = closure(n, bounded)
            check(len(S) == sizes[bounded][n - 1],
                  f"[{tag}] |FD({n})| = {len(S)} (closure of projections)")
            if n <= 3:
                check(S == monotone_functions(n, bounded),
                      f"[{tag}] FD({n}) = all {'' if bounded else 'nonconstant '}monotone functions")
            # variable permutations are automorphisms
            perms = list(permutations(range(n)))
            ok = True
            for s in perms:
                img = {f: act(s, f) for f in S}
                if set(img.values()) != S:
                    ok = False
                for f in S:
                    for g in S:
                        if img[f & g] != img[f] & img[g] or img[f | g] != img[f] | img[g]:
                            ok = False
            check(ok, f"[{tag}] n={n}: every variable permutation is a lattice automorphism")
            # full automorphism group
            if n <= 3:
                autos = lattice_automorphisms(S)
                induced = [any(all(phi[f] == act(s, f) for f in S) for phi in autos) for s in perms]
                every_is_perm = all(any(all(phi[f] == act(s, f) for f in S) for s in perms)
                                    for phi in autos)
                check(len(autos) == math.factorial(n) and every_is_perm and all(induced),
                      f"[{tag}] n={n}: brute force |Aut(FD)| = {len(autos)} = {n}!, all are "
                      f"variable permutations")
                fixed = {f for f in S if all(phi[f] == f for phi in autos)}
            else:
                J = join_irreducibles(S)
                jautos = poset_automorphisms(J)
                exp_J = (1 << n) - 2 if not bounded else (1 << n)
                check(len(J) == exp_J and len(jautos) == math.factorial(n),
                      f"[{tag}] n={n}: |J(FD)| = {len(J)}, |Aut(J)| = {len(jautos)} = {n}! "
                      f"(Birkhoff: Aut(FD) = Aut(J)), so Aut(FD(4)) = S_4")
                fixed = {f for f in S if all(act(s, f) == f for s in perms)}
            ks = range(1, n + 1) if not bounded else range(0, n + 2)
            check(fixed == {threshold(n, k) for k in ks},
                  f"[{tag}] n={n}: Aut-fixed elements = thresholds k in "
                  f"{list(ks)[0]}..{list(ks)[-1]} ({len(fixed)} elements)")
            L = longest_chain(fixed)
            lengths[(bounded, n)] = L
            check(L == (n - 1 if not bounded else n + 1),
                  f"[{tag}] n={n}: fixed lattice is a chain, maximal chain length {L} edges "
                  f"({L + 1} elements); log p(n) would need b^{L} = {P[n]}")

    # ------------------------------------------------ the logarithm clause
    print()
    for bounded in (False, True):
        for elems in (False, True):
            Ls = [lengths[(bounded, n)] + (1 if elems else 0) for n in (1, 2, 3)]
            # b^L1 = 1, b^L2 = 2, b^L3 = 3 with consecutive L: b = 2 then 4 = 3
            consecutive = Ls[1] == Ls[0] + 1 and Ls[2] == Ls[1] + 1
            # any base b>0: L2 = log_b 2 and L3 = log_b 3 force 2^L3 = 3^L2
            bad = 2 ** Ls[2] != 3 ** Ls[1]
            check(consecutive and bad,
                  f"reading bounded={bounded}, count elements={elems}: lengths at n=1,2,3 = {Ls}; "
                  f"b^{Ls[0]} = 1, b^{Ls[1]} = 2 force b = 2, then b^{Ls[2]} = 4 != 3; "
                  f"also 2^{Ls[2]} != 3^{Ls[1]}")
    check(all(2 ** a != 3 ** c for a in range(0, 60) for c in range(0, 60) if (a, c) != (0, 0)),
          "2^a = 3^c only for a = c = 0 (checked a, c < 60; proved in general in Lean/report)")
    check(abs(math.log(P[2]) - 1) > 0.3, "natural log: ln p(2) = ln 2 = 0.693... != 1")

    # rounding readings for common bases (free lattice, edges): fails for some n <= 5
    for name, b in (("2", 2.0), ("e", math.e), ("10", 10.0)):
        for rnd_name, rnd in (("floor", math.floor), ("ceil", math.ceil), ("round", round)):
            bad_n = [n for n in range(1, 61) if rnd(math.log(P[n], b)) != n - 1]
            check(bool(bad_n) and bad_n[0] <= 5,
                  f"rounded reading {rnd_name}(log_{name} p(n)) = n-1 fails first at n = {bad_n[0]}")
    # growth: log p(n) / (n-1) -> 0, so no base works even eventually
    ratios = [math.log(P[n]) / (n - 1) for n in (10, 20, 40, 60)]
    print("     ln p(n)/(n-1) at n=10,20,40,60:", ", ".join(f"{r:.4f}" for r in ratios))
    check(all(ratios[i] > ratios[i + 1] for i in range(3)),
          "ln p(n)/(n-1) is decreasing on these samples (it tends to 0; see report)")

    # single-automorphism reading (not the stated one): chain lengths of Fix(sigma)
    print()
    for n in (2, 3):
        S = closure(n, False)
        for s in permutations(range(n)):
            F = {f for f in S if act(s, f) == f}
            print(f"     n={n}, sigma={s}: |Fix| = {len(F)}, longest chain = {longest_chain(F)}")
    print("     (any integer lengths L2, L3 fail: 2^L3 != 3^L2 unless L2 = L3 = 0, and b^0 != 2)")

    print()
    print("ALL CHECKS PASSED" if OK else "SOME CHECK FAILED")
    return 0 if OK else 1


if __name__ == "__main__":
    sys.exit(main())
