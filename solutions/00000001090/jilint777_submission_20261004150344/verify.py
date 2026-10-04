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
     and the 768 permutations used in Lean are distinct automorphisms.
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
    print("|M11| = 7920 does not divide 660, so M11 is not a subgroup of a group of order 660:", 660 % 7920 != 0)
    print("ALL CHECKS PASSED")


if __name__ == "__main__":
    main()
