"""Checks for conjecture 00000002141 (Python 3 standard library; nauty optional).

1. The four graphs A1, B1, A2, B2 on 10 vertices are 4-regular.
2. A1, B1 have equal characteristic polynomials, and so do A2, B2, computed
   exactly in two ways (Faddeev-LeVerrier, and det(xI - A) by exact Gaussian
   elimination at 11 points); the two pairs have different polynomials.
3. A1 !~ B1, A2 !~ B2, A1 !~ A2, A1 !~ B2 by an exhaustive backtracking
   isomorphism search (complete, with degree-preserving pruning only).
4. If nauty's geng is installed: enumerate all regular graphs on n <= 10
   vertices and list every cospectral family (none for n < 10; at n = 10
   two 4-regular pairs and their two 5-regular complement pairs).
"""

import shutil
import subprocess
from fractions import Fraction

E = {
    "A1": [(0,3),(0,5),(0,7),(0,9),(1,4),(1,5),(1,7),(1,9),(2,5),(2,6),
           (2,7),(2,8),(3,6),(3,8),(3,9),(4,6),(4,8),(4,9),(5,7),(6,8)],
    "B1": [(0,3),(0,5),(0,7),(0,8),(1,4),(1,5),(1,8),(1,9),(2,5),(2,6),
           (2,7),(2,9),(3,6),(3,7),(3,8),(4,6),(4,8),(4,9),(5,7),(6,9)],
    "A2": [(0,3),(0,5),(0,7),(0,8),(1,4),(1,5),(1,7),(1,9),(2,5),(2,6),
           (2,8),(2,9),(3,6),(3,7),(3,8),(4,6),(4,8),(4,9),(5,7),(6,9)],
    "B2": [(0,3),(0,4),(0,6),(0,7),(1,5),(1,6),(1,8),(1,9),(2,5),(2,7),
           (2,8),(2,9),(3,4),(3,6),(3,7),(4,8),(4,9),(5,7),(5,8),(6,9)],
}


def adj(edges, n=10):
    A = [[0] * n for _ in range(n)]
    for u, v in edges:
        A[u][v] = A[v][u] = 1
    return A


def charpoly_fl(A):
    """Faddeev-LeVerrier; returns coefficients c_0..c_n of det(xI - A)."""
    n = len(A)
    M = [[0] * n for _ in range(n)]
    c = [0] * (n + 1)
    c[n] = 1
    for k in range(1, n + 1):
        AM = [[sum(A[i][l] * M[l][j] for l in range(n)) for j in range(n)] for i in range(n)]
        M = [[AM[i][j] + (c[n - k + 1] if i == j else 0) for j in range(n)] for i in range(n)]
        AM = [[sum(A[i][l] * M[l][j] for l in range(n)) for j in range(n)] for i in range(n)]
        tr = sum(AM[i][i] for i in range(n))
        assert tr % k == 0
        c[n - k] = -tr // k
    return c


def det(M):
    M = [[Fraction(x) for x in row] for row in M]
    n, d = len(M), Fraction(1)
    for col in range(n):
        p = next((i for i in range(col, n) if M[i][col] != 0), None)
        if p is None:
            return Fraction(0)
        if p != col:
            M[col], M[p] = M[p], M[col]
            d = -d
        d *= M[col][col]
        for i in range(col + 1, n):
            f = M[i][col] / M[col][col]
            M[i] = [a - f * b for a, b in zip(M[i], M[col])]
    return d


def char_values(A):
    n = len(A)
    return [det([[(x if i == j else 0) - A[i][j] for j in range(n)] for i in range(n)])
            for x in range(n + 1)]


def isomorphic(A, B):
    n = len(A)
    dA = [sum(r) for r in A]
    dB = [sum(r) for r in B]
    if sorted(dA) != sorted(dB):
        return False
    m = [-1] * n
    used = [False] * n

    def bt(i):
        if i == n:
            return True
        for j in range(n):
            if not used[j] and dA[i] == dB[j] and all(A[i][k] == B[j][m[k]] for k in range(i)):
                m[i], used[j] = j, True
                if bt(i + 1):
                    return True
                m[i], used[j] = -1, False
        return False

    return bt(0)


def g6_to_adj(s):
    s = s.strip()
    n = ord(s[0]) - 63
    bits = []
    for ch in s[1:]:
        v = ord(ch) - 63
        bits += [(v >> (5 - i)) & 1 for i in range(6)]
    A = [[0] * n for _ in range(n)]
    k = 0
    for j in range(1, n):
        for i in range(j):
            A[i][j] = A[j][i] = bits[k]
            k += 1
    return A


def main():
    G = {k: adj(v) for k, v in E.items()}
    for k, A in G.items():
        assert all(sum(r) == 4 for r in A) and all(A[i][i] == 0 for i in range(10))
    cp = {k: charpoly_fl(A) for k, A in G.items()}
    cv = {k: char_values(A) for k, A in G.items()}
    for k in G:
        # the two methods agree: evaluate the Faddeev-LeVerrier polynomial at x = 0..10
        assert [sum(c * x ** i for i, c in enumerate(cp[k])) for x in range(11)] == cv[k]
    assert cp["A1"] == cp["B1"] and cp["A2"] == cp["B2"] and cp["A1"] != cp["A2"]
    print("charpoly(A1) = charpoly(B1) =", cp["A1"])
    print("charpoly(A2) = charpoly(B2) =", cp["A2"])
    for a, b in [("A1", "B1"), ("A2", "B2"), ("A1", "A2"), ("A1", "B2"), ("B1", "A2"), ("B1", "B2")]:
        assert not isomorphic(G[a], G[b]), (a, b)
    print("A1, B1, A2, B2 pairwise non-isomorphic (exhaustive search)")
    geng = shutil.which("nauty-geng") or shutil.which("geng")
    if geng:
        for n in range(1, 11):
            for k in range(n):
                out = subprocess.run([geng, "-q", "-d%d" % k, "-D%d" % k, str(n)],
                                     capture_output=True, text=True).stdout.split()
                groups = {}
                for s in out:
                    groups.setdefault(tuple(charpoly_fl(g6_to_adj(s))), []).append(s)
                fam = [v for v in groups.values() if len(v) > 1]
                if fam:
                    print("n=%d, %d-regular: %d graphs, cospectral families %s" % (n, k, len(out), fam))
                    assert n == 10 and k in (4, 5) and [len(f) for f in fam] == [2, 2]
        print("no cospectral regular graphs below order 10; at order 10 exactly two "
              "4-regular pairs and two 5-regular pairs")
    else:
        print("(nauty not installed: enumeration step skipped)")
    print("ALL CHECKS PASSED")


if __name__ == "__main__":
    main()
