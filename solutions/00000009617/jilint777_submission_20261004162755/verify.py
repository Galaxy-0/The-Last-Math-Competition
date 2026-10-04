"""Independent checks for conjecture 00000009617 (Python 3 standard library only).

Even shift X: bi-infinite 0/1 sequences in which every run of 1s bounded by 0s
on both sides has even length (forbidden blocks 0 1^(2k+1) 0).

Checks
  1. Three descriptions of the language L(X) agree on all words of length <= 14:
     (a) forbidden blocks, (b) parities of the inner runs of 1s, (c) labels of
     paths in the 2-state Fischer graph A-0->A, A-1->B, B-1->A.
  2. Presentations: no labelled graph with 0 or 1 vertices presents X; among
     all 2^8 labelled graphs on 2 vertices, the ones presenting X are listed
     (the Fischer graph and its relabelling), and they are right-resolving.
  3. Hankel matrix H[u][v] = [uv in L]: the 3x3 minor rows (11, 0, 01) x
     columns (0, 10, 1) has determinant -1; the truncation to all words of
     length <= 6 has rank 3 over Q and over GF(2), GF(3), GF(5), GF(7); every
     row equals one of 4 vectors (3 nonzero follower sets + the zero row).
  4. Disclosure: the Boolean (OR/AND) rank of H is 2.
"""

from fractions import Fraction
from itertools import product

MAXLEN = 14


def words(maxlen, minlen=0):
    for n in range(minlen, maxlen + 1):
        for p in product("01", repeat=n):
            yield "".join(p)


# ---------- 1. the language, three ways ----------

def in_L_forbidden(w):
    """(a) no factor 0 1^(2k+1) 0."""
    n = len(w)
    for i in range(n):
        if w[i] != "0":
            continue
        for j in range(i + 2, n):
            if w[j] == "0":
                if all(c == "1" for c in w[i + 1:j]) and (j - i - 1) % 2 == 1:
                    return False
                break
    return True


def in_L_runs(w):
    """(b) inner runs of 1s (between two 0s of w) have even length."""
    return all(len(r) % 2 == 0 for r in w.split("0")[1:-1])


FISCHER = {("A", "0"): {"A"}, ("A", "1"): {"B"}, ("B", "1"): {"A"}}


def path_states(graph, states, w):
    """Subset simulation: end states of paths labelled w starting in `states`."""
    cur = set(states)
    for c in w:
        cur = set().union(*[graph.get((s, c), set()) for s in cur]) if cur else set()
    return cur


def in_L_graph(w):
    """(c) w labels a path in the Fischer graph (it is essential, so finite path
    labels = blocks of bi-infinite path labels)."""
    return bool(path_states(FISCHER, {"A", "B"}, w))


ALLW = list(words(MAXLEN))
for w in ALLW:
    a, b, c = in_L_forbidden(w), in_L_runs(w), in_L_graph(w)
    assert a == b == c, w
print(f"L(X): forbidden blocks == run parities == Fischer-graph paths on all {len(ALLW)} words of length <= {MAXLEN}")
L = {w for w in ALLW if in_L_forbidden(w)}

# ---------- 2. presentations ----------

def essential(n, edges):
    """Prune vertices without in- or out-edges until stable (X_G only depends on
    the essential part)."""
    V = set(range(n))
    E = set(edges)
    while True:
        outd = {p for (p, a, q) in E}
        ind = {q for (p, a, q) in E}
        keep = V & outd & ind
        if keep == V:
            return V, E
        V = keep
        E = {(p, a, q) for (p, a, q) in E if p in V and q in V}


def graph_lang(n, edges, maxlen):
    """Blocks of X_G of length <= maxlen = labels of finite paths in the essential part."""
    V, E = essential(n, edges)
    g = {}
    for (p, a, q) in E:
        g.setdefault((p, a), set()).add(q)
    return {w for w in words(maxlen) if V and path_states(g, V, w)} | ({""} if V else set())


CMP = 8
Lcmp = {w for w in L if len(w) <= CMP}
all_edges = lambda n: [(p, a, q) for p in range(n) for a in "01" for q in range(n)]

presenting = {}
for n in range(0, 3):
    cand = all_edges(n)
    found = []
    for mask in range(1 << len(cand)):
        E = [cand[i] for i in range(len(cand)) if mask >> i & 1]
        if graph_lang(n, E, CMP) == Lcmp:
            found.append(E)
    presenting[n] = found
    print(f"{n}-vertex labelled graphs whose shift has the same blocks of length <= {CMP} as X: {len(found)}")
assert presenting[0] == [] and presenting[1] == []
# with one vertex the loop label set T gives T*; show the distinguishing words
for T in [set(), {"0"}, {"1"}, {"0", "1"}]:
    tl = {w for w in words(3) if all(ch in T for ch in w)}
    diff = sorted((tl ^ {w for w in L if len(w) <= 3}), key=lambda s: (len(s), s))
    print(f"  one vertex, loop labels {sorted(T)}: first difference {diff[0]!r}")
for E in presenting[2]:
    rr = all(len({q for (p2, a2, q) in E if (p2, a2) == (p, a)}) <= 1 for p in range(2) for a in "01")
    print(f"  2-vertex presentation {sorted(E)} right-resolving={rr}")
    # it must be the Fischer graph up to renaming the two vertices
    ren = [{0: "A", 1: "B"}, {0: "B", 1: "A"}]
    assert any({(r[p], a, r[q]) for (p, a, q) in E} == {("A", "0", "A"), ("A", "1", "B"), ("B", "1", "A")} for r in ren)
assert len(presenting[2]) == 2
print("Fischer count = minimal number of states of any presentation = 2")

# ---------- 3. Hankel matrix ----------

def H(u, v):
    return 1 if in_L_forbidden(u + v) else 0


def det3(m):
    return (m[0][0] * (m[1][1] * m[2][2] - m[1][2] * m[2][1])
            - m[0][1] * (m[1][0] * m[2][2] - m[1][2] * m[2][0])
            + m[0][2] * (m[1][0] * m[2][1] - m[1][1] * m[2][0]))


rows, cols = ["11", "0", "01"], ["0", "10", "1"]
M = [[H(u, v) for v in cols] for u in rows]
print("minor rows", rows, "cols", cols, "=", M, "det =", det3(M))
assert M == [[1, 1, 1], [1, 0, 1], [0, 1, 1]] and det3(M) == -1
inv = [[1, 0, -1], [1, -1, 0], [-1, 1, 1]]
prod = [[sum(M[i][k] * inv[k][j] for k in range(3)) for j in range(3)] for i in range(3)]
assert prod == [[1, 0, 0], [0, 1, 0], [0, 0, 1]]
print("integer inverse", inv, "verified: the minor is unimodular")


def rank_Q(A):
    A = [[Fraction(x) for x in r] for r in A]
    rk = 0
    for c in range(len(A[0])):
        piv = next((i for i in range(rk, len(A)) if A[i][c] != 0), None)
        if piv is None:
            continue
        A[rk], A[piv] = A[piv], A[rk]
        for i in range(len(A)):
            if i != rk and A[i][c] != 0:
                f = A[i][c] / A[rk][c]
                A[i] = [x - f * y for x, y in zip(A[i], A[rk])]
        rk += 1
    return rk


def rank_p(A, p):
    A = [[x % p for x in r] for r in A]
    rk = 0
    for c in range(len(A[0])):
        piv = next((i for i in range(rk, len(A)) if A[i][c]), None)
        if piv is None:
            continue
        A[rk], A[piv] = A[piv], A[rk]
        invp = pow(A[rk][c], p - 2, p)
        A[rk] = [x * invp % p for x in A[rk]]
        for i in range(len(A)):
            if i != rk and A[i][c]:
                f = A[i][c]
                A[i] = [(x - f * y) % p for x, y in zip(A[i], A[rk])]
        rk += 1
    return rk


W6 = list(words(6))
HM = [[H(u, v) for v in W6] for u in W6]
rq = rank_Q(HM)
print(f"Hankel truncation on all {len(W6)} words of length <= 6: rank over Q = {rq}")
assert rq == 3
for p in (2, 3, 5, 7):
    r = rank_p(HM, p)
    print(f"  rank over GF({p}) = {r}")
    assert r == 3
W6n = [w for w in W6 if w]
HMn = [[H(u, v) for v in W6n] for u in W6n]
assert rank_Q(HMn) == 3
print("  (same rank 3 when the empty word is excluded from rows and columns)")

# Myhill-Nerode: rows are follower-set indicators; only 4 distinct rows occur
W8 = list(words(8))
distinct = {tuple(H(u, v) for v in W8) for u in W8}
print(f"distinct rows of H on words of length <= 8 (columns of length <= 8): {len(distinct)} (one is the zero row)")
assert len(distinct) == 4 and tuple([0] * len(W8)) in distinct

# ---------- 4. Boolean rank (disclosure) ----------
rN = [H("", v) for v in W8]
rE = [H("0", v) for v in W8]
rO = [H("01", v) for v in W8]
assert all(n == (e | o) for n, e, o in zip(rN, rE, rO))
# fooling set {(0,0), (01,10)}: H[0][0]=H[01][10]=1 but H[0][10]=0
assert H("0", "0") == 1 and H("01", "10") == 1 and H("0", "10") == 0
print("Boolean rank of H is 2: row(eps) = row(0) OR row(01); fooling set {(0,0),(01,10)} (disclosure)")
# over Q, row(eps) is NOT row(0)+row(01): they overlap on 1^k
assert any(e and o for e, o in zip(rE, rO))

print("ALL CHECKS PASSED: Fischer count 2, Hankel rank 3 over every field")
