#!/usr/bin/env python3
"""Independent check (Python 3 standard library only) for conjecture 00000001090.

The conjecture concerns MDS codes over GF(3) of type [12,6], i.e. ternary [12,6,7] codes.
We check, by methods different from the Lean proof:
  1. no ternary [8,2,7] code exists (exhaustive over all pairs of words of weight >= 7);
     shortening a [12,6,7] code four times would give one;
  2. the bound n <= k+2 for ternary codes with all nonzero weights >= n-k+1, exhaustively
     for (n,k) = (5,2), (6,3) (systematic form is forced, see report);
  3. the Griesmer bound already excludes [12,6,7]_3;
  4. random [12,6] generator matrices: the explicit construction of the proof always yields a
     nonzero codeword of weight <= 6, matching exhaustive minimum-distance computation;
  5. the tetracode is a [4,2,3] MDS code and the Golay code is a [12,6,6] code;
  6. the repeated-pair [12,6,2] code has exactly 2^6 * 6! = 46080 permutation automorphisms,
     and the 768 permutations used in Lean are distinct automorphisms;
  7. the monomial class of the ternary Golay code (the unique [12,6,6]_3 code up to monomial
     equivalence) splits into exactly 5 permutation-equivalence classes with |PAut| =
     108, 120, 432, 660, 7920; golay has |PAut| = 660 and golay' (column 6 doubled) has
     |PAut| = 7920 = |M11|; the 720 automorphisms of golay' listed in Lean are re-checked.
"""
import itertools
import random
from math import factorial

Q = 3


def wt(w):
    return sum(1 for x in w if x % Q)


def span(G):
    k, n = len(G), len(G[0])
    for m in itertools.product(range(Q), repeat=k):
        yield m, tuple(sum(m[i] * G[i][j] for i in range(k)) % Q for j in range(n))


def min_dist(G):
    return min(wt(w) for m, w in span(G) if any(m))


def check_no_8_2_7():
    heavy = [v for v in itertools.product(range(Q), repeat=8) if wt(v) >= 7]
    assert len(heavy) == 8 * 2 ** 7 + 2 ** 8 == 1280
    hs = set(heavy)
    found = 0
    for u in heavy:
        for v in heavy:
            # the 8 nonzero combinations a*u+b*v must all be heavy (in particular nonzero)
            ok = True
            for a, b in ((1, 1), (1, 2), (2, 1), (2, 2)):
                w = tuple((a * x + b * y) % Q for x, y in zip(u, v))
                if w not in hs:
                    ok = False
                    break
            if ok:  # u, 2u, v, 2v are heavy since heavy is closed under scaling
                found += 1
    print("pairs (u,v) in F_3^8 spanning a code with all 8 nonzero weights >= 7:", found)
    assert found == 0
    # the best [8,2] ternary code has d = 6
    best = 0
    for A in itertools.product(range(Q), repeat=12):
        G = [[1, 0] + list(A[:6]), [0, 1] + list(A[6:])]
        best = max(best, min_dist(G))
    print("largest minimum distance of a systematic ternary [8,2] code:", best)
    assert best == 6


def check_small_bound():
    for (n, k) in ((5, 2), (6, 3)):
        d = n - k + 1
        count = 0
        for A in itertools.product(range(Q), repeat=k * (n - k)):
            G = [[1 if i == j else 0 for j in range(k)] + list(A[i * (n - k):(i + 1) * (n - k)])
                 for i in range(k)]
            if min_dist(G) >= d:
                count += 1
        print(f"systematic ternary [{n},{k}] codes with minimum distance >= {d}: {count}")
        assert count == 0


def check_griesmer():
    n_min = sum(-(-7 // Q ** i) for i in range(6))
    print("Griesmer bound for a ternary [n,6,7] code: n >=", n_min)
    assert n_min == 14 > 12


def rank_mod3(rows):
    rows = [list(r) for r in rows]
    r = 0
    ncols = len(rows[0]) if rows else 0
    for c in range(ncols):
        piv = next((i for i in range(r, len(rows)) if rows[i][c] % 3), None)
        if piv is None:
            continue
        rows[r], rows[piv] = rows[piv], rows[r]
        inv = rows[r][c] % 3  # 1*1 = 2*2 = 1 mod 3
        rows[r] = [(x * inv) % 3 for x in rows[r]]
        for i in range(len(rows)):
            if i != r and rows[i][c] % 3:
                f = rows[i][c]
                rows[i] = [(x - f * y) % 3 for x, y in zip(rows[i], rows[r])]
        r += 1
    return r


def kernel_vectors(G, cols):
    """All messages m with (mG)_j = 0 for j in cols (brute force over 3^k)."""
    k = len(G)
    return [m for m in itertools.product(range(Q), repeat=k)
            if all(sum(m[i] * G[i][j] for i in range(k)) % Q == 0 for j in cols)]


def check_random_12_6(trials=300):
    rng = random.Random(1090)
    done = 0
    while done < trials:
        G = [[rng.randrange(3) for _ in range(12)] for _ in range(6)]
        if rank_mod3(G) < 6:
            continue
        done += 1
        K = kernel_vectors(G, range(4))          # messages vanishing on coords 0..3
        assert len(K) >= 9                        # kernel of a map F_3^6 -> F_3^4
        m1 = next(m for m in K if any(m))
        m2 = next(m for m in K if any(m) and m not in
                  {tuple((a * x) % 3 for x in m1) for a in range(3)})
        words = []
        for a, b in itertools.product(range(3), repeat=2):
            if (a, b) == (0, 0):
                continue
            m = tuple((a * x + b * y) % 3 for x, y in zip(m1, m2))
            words.append(tuple(sum(m[i] * G[i][j] for i in range(6)) % 3 for j in range(12)))
        total = sum(wt(w) for w in words)
        assert total <= 48 and min(wt(w) for w in words) <= 6
        assert min_dist(G) <= 6
    print(f"{trials} random [12,6] ternary codes: the construction always gives weight <= 6")


def check_examples():
    tetra = [[1, 0, 1, 1], [0, 1, 1, 2]]
    assert rank_mod3(tetra) == 2 and min_dist(tetra) == 3
    print("tetracode: [4,2,3] MDS code (so n <= k+2 is sharp)")
    A = [[0, 1, 1, 1, 1, 1], [1, 0, 1, 2, 2, 1], [1, 1, 0, 1, 2, 2],
         [1, 2, 1, 0, 1, 2], [1, 2, 2, 1, 0, 1], [1, 1, 2, 2, 1, 0]]
    golay = [[1 if i == j else 0 for j in range(6)] + A[i] for i in range(6)]
    dist = {}
    for m, w in span(golay):
        dist[wt(w)] = dist.get(wt(w), 0) + 1
    print("Golay code weight distribution:", dict(sorted(dist.items())))
    assert dist == {0: 1, 6: 264, 9: 440, 12: 24}


GOLAY_A = [[0, 1, 1, 1, 1, 1], [1, 0, 1, 2, 2, 1], [1, 1, 0, 1, 2, 2],
           [1, 2, 1, 0, 1, 2], [1, 2, 2, 1, 0, 1], [1, 1, 2, 2, 1, 0]]
GOLAY = [[1 if i == j else 0 for j in range(6)] + GOLAY_A[i] for i in range(6)]
GOLAY2 = [[(g[j] * (2 if j == 6 else 1)) % 3 for j in range(12)] for g in GOLAY]  # golay'


def hexad_preserving_perms(code):
    """All permutations sigma of 12 coordinates mapping the supports of weight-6 words
    (which are the same for every code monomially equivalent to `code`) to themselves."""
    hexes = set(frozenset(j for j in range(12) if w[j]) for w in code if wt(w) == 6)
    assert len(hexes) == 132
    by = {}
    for h in hexes:
        by.setdefault(max(h), []).append(h)
    out = []
    def rec(img, used):
        t = len(img)
        if t == 12:
            out.append(tuple(img)); return
        for c in range(12):
            if c in used: continue
            img.append(c)
            if all(frozenset(img[j] for j in h) in hexes for h in by.get(t, [])):
                rec(img, used | {c})
            img.pop()
    rec([], frozenset())
    return out


def norm(v):  # sign vectors modulo the global sign -1
    return v if v[0] == 1 else tuple((2 * x) % 3 for x in v)


def check_golay_classes():
    C = {w for m, w in span(GOLAY)}
    H = hexad_preserving_perms(C)
    print("hexad-preserving permutations (M12):", len(H))
    assert len(H) == 95040
    # diagonal automorphisms of C are only +-1
    diag = [e for e in itertools.product((1, 2), repeat=12)
            if all(tuple((g[j] * e[j]) % 3 for j in range(12)) in C for g in GOLAY)]
    assert sorted(diag) == [(1,) * 12, (2,) * 12]
    # for each sigma in H, the signs s with c -> s*(c o sigma) an automorphism of C
    w12 = [w for w in C if wt(w) == 12]
    w0 = w12[0]
    S = []
    for sig in H:
        rows = [[g[sig[j]] for j in range(12)] for g in GOLAY]
        w0s = [w0[sig[j]] for j in range(12)]
        sols = set()
        for c in w12:
            s = tuple((c[j] * w0s[j]) % 3 for j in range(12))
            if all(tuple((s[j] * r[j]) % 3 for j in range(12)) in C for r in rows):
                sols.add(s)
        assert len(sols) == 2  # exactly +-s: MAut(C) = 2.M12 of order 190080
        S.append(norm(min(sols)))
    print("monomial automorphism group order:", 2 * len(H))
    # The code C_d = C*diag(d) (d in {1,2}^12 modulo +-1) has
    # PAut(C_d) = {sigma in H : s(sigma) * (d o sigma) = +-d}.
    def paut_order(d):
        return sum(1 for sig, s in zip(H, S)
                   if norm(tuple((s[j] * d[sig[j]] * d[j]) % 3 for j in range(12))) == (1,) * 12)
    reps = {}
    cand = [tuple([1] * 12), tuple(2 if j == 6 else 1 for j in range(12))]
    rng = __import__("random").Random(1090)
    while len(reps) < 5 and len(cand) < 400:
        d = cand.pop(0) if cand else tuple([1] + [rng.choice((1, 2)) for _ in range(11)])
        o = paut_order(d)
        reps.setdefault(o, d)
        if not cand:
            cand.append(tuple([1] + [rng.choice((1, 2)) for _ in range(11)]))
    orders = sorted(reps)
    print("PAut orders found:", orders, "orbit sizes:", [95040 // o for o in orders])
    assert orders == [108, 120, 432, 660, 7920]
    # distinct stabilizer orders => distinct orbits; the orbits already cover all 2^11 twists
    assert sum(95040 // o for o in orders) == 2 ** 11
    assert paut_order(tuple([1] * 12)) == 660
    assert paut_order(tuple(2 if j == 6 else 1 for j in range(12))) == 7920
    print("Golay code (column scaling d): |PAut| = 660 for golay, 7920 for golay' (column 6 doubled)")
    print("the monomial class of the Golay code has exactly 5 permutation classes, |PAut| =", orders)
    print("orders 108, 120, 432 do not divide 132:", all(132 % o for o in (108, 120, 432)))
    return H, S


def check_lean_golay_auts():
    """Cross-check the lists H1, H2 of lean4/Main.lean: golayAuts = {h o k : h in H1, k in H2}."""
    import os, re
    path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "lean4", "Main.lean")
    try:
        src = open(path, encoding="utf8").read()
    except OSError:
        print("lean4/Main.lean not found; skipping the golayAuts cross-check")
        return

    def grab(name):
        body = src[src.index("def " + name + " :"):]
        body = body[body.index("[") + 1:body.index("]\n\n")]
        return [tuple(int(x) for x in m.split(","))
                for m in re.findall(r"\[([0-9, ]+)\]", body)]
    H1, H2 = grab("H1"), grab("H2")
    assert len(H1) == 30 and len(H2) == 24
    C2 = {w for m, w in span(GOLAY2)}
    def is_aut(sig):
        return sorted(sig) == list(range(12)) and \
            all(tuple(g[sig[j]] for j in range(12)) in C2 for g in GOLAY2)
    prods = {tuple(h[k[j]] for j in range(12)) for h in H1 for k in H2}
    assert len(prods) == 720 and all(is_aut(s) for s in prods)
    assert min_dist(GOLAY2) == 6 and rank_mod3(GOLAY2) == 6
    print("golay' is a [12,6,6] code; the 720 products h o k (h in H1, k in H2) from Lean are "
          "distinct permutation automorphisms")


def in_pair_code(w):
    return all(w[2 * i] == w[2 * i + 1] for i in range(6))


def check_pair_code():
    G = [[1 if j // 2 == i else 0 for j in range(12)] for i in range(6)]
    words = [w for m, w in span(G)]
    supports2 = {frozenset(j for j in range(12) if w[j]) for w in words if wt(w) == 2}
    pairs = {frozenset((2 * i, 2 * i + 1)) for i in range(6)}
    assert supports2 == pairs
    # every automorphism permutes the supports of weight-2 words, i.e. the 6 pairs;
    # conversely every pair-preserving permutation is an automorphism. Count them:
    count = 0
    for pi in itertools.permutations(range(6)):
        for s in range(64):
            sigma = [2 * pi[j // 2] + ((j % 2) ^ ((s >> (j // 2)) & 1)) for j in range(12)]
            assert sorted(sigma) == list(range(12))
            assert all(in_pair_code([g[sigma[j]] for j in range(12)]) for g in G)
            count += 1
    print("pair code [12,6,2]: permutation automorphisms =", count, "= 2^6 * 6! =", 64 * factorial(6))
    assert count == 46080 > 660
    # the 768 permutations of the Lean file
    def blk(t, i):
        return (i + t) % 6 if t < 6 else (t + 12 - i) % 6
    lean = [tuple(2 * blk(t, j // 2) + (j % 2 + s // 2 ** (j // 2)) % 2 for j in range(12))
            for t in range(12) for s in range(64)]
    assert len(set(lean)) == 768
    for sigma in lean:
        assert sorted(sigma) == list(range(12))
        assert all(in_pair_code([g[sigma[j]] for j in range(12)]) for g in G)
    print("the 768 permutations listed in Lean are distinct automorphisms of the pair code")


def main():
    check_no_8_2_7()
    check_small_bound()
    check_griesmer()
    check_random_12_6()
    check_examples()
    check_pair_code()
    check_golay_classes()
    check_lean_golay_auts()
    print("|M11| = 7920 does not divide 660, so M11 is not a subgroup of a group of order 660:",
          660 % 7920 != 0)
    print("ALL CHECKS PASSED")


if __name__ == "__main__":
    main()
