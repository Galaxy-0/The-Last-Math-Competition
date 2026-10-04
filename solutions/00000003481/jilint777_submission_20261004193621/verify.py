#!/usr/bin/env python3
"""Independent check for conjecture 00000003481 (Thue numbers of trees).
Python 3 standard library only.

A Thue (nonrepetitive) colouring of a graph is a vertex colouring such that the colour
sequence of every path (any sequence of distinct vertices, consecutive ones adjacent) has
no square factor xx with x nonempty.  pi(G) is the least number of colours of one.

Checks:
  [A] pi(K2) = 2 and pi(P4) = 3 by plain enumeration of all colourings and all paths.
  [B] All trees with n <= 12 vertices (up to isomorphism; counts compared with OEIS A000055):
      pi(T) is computed for each (and the colouring found is re-checked on all paths);
      max pi = 3; the trees violating pi(T) <= 2 log Delta(T) are counted (base 2 and base e).
  [C] Complete binary trees: pi = 3 for depths 2..5 and pi = 4 for depth 6 (two different
      backtracking searches); Delta = 3 and 2 log2 3 = 3.17 < 4.
  [D] The pi <= 4 construction for trees: a square-free ternary word w, the Kuendgen-Pelsmajer
      insertion of a 4th letter, and the depth colouring; checked nonrepetitive on every tree
      with n <= 12 vertices (rooted at every vertex) and on complete binary trees up to depth 8.
"""
import itertools
import math
import sys

# ----------------------------------------------------------------- basic predicates

def has_square(seq):
    L = len(seq)
    for h in range(1, L // 2 + 1):
        for s in range(L - 2 * h + 1):
            if seq[s:s + h] == seq[s + h:s + 2 * h]:
                return True
    return False


def all_paths(adj):
    """All paths (as vertex lists, both orientations, including single vertices)."""
    res = []
    for v in range(len(adj)):
        stack = [[v]]
        while stack:
            p = stack.pop()
            res.append(p)
            for w in adj[p[-1]]:
                if w not in p:
                    stack.append(p + [w])
    return res


def is_nonrepetitive(adj, col, paths=None):
    if paths is None:
        paths = all_paths(adj)
    return all(not has_square([col[v] for v in p]) for p in paths)


def thue_bruteforce(adj, maxc=4):
    """Least k with a Thue k-colouring, by enumerating ALL colourings (small graphs only)."""
    paths = all_paths(adj)
    for k in range(1, maxc + 1):
        for col in itertools.product(range(k), repeat=len(adj)):
            if is_nonrepetitive(adj, col, paths):
                return k, col
    return None, None

# ----------------------------------------------------------------- backtracking search

def bt_colour(adj, k, order, symbreak=True):
    """Search for a Thue k-colouring; vertices coloured in `order` (each a neighbour of an
    earlier one).  When vertex order[i] is coloured, every path through it inside the coloured
    part ends at it, so only squares ending at it must be checked."""
    n = len(adj)
    pos = {v: i for i, v in enumerate(order)}
    back = []
    for i, v in enumerate(order):
        ps = []
        stack = [[v]]
        while stack:
            p = stack.pop()
            if len(p) >= 2:
                ps.append(p)
            for w in adj[p[-1]]:
                if pos[w] < i and w not in p:
                    stack.append(p + [w])
        back.append(ps)
    col = {}

    def ok(i):
        for p in back[i]:
            L = len(p)
            for h in range(1, L // 2 + 1):
                if all(col[p[j]] == col[p[j + h]] for j in range(h)):
                    return False
        return True

    sys.setrecursionlimit(10000)

    def rec(i, used):
        if i == n:
            return True
        v = order[i]
        top = min(k, used + 1) if symbreak else (1 if i == 0 else k)
        for c in range(top):
            col[v] = c
            if ok(i) and rec(i + 1, max(used, c + 1)):
                return True
        del col[v]
        return False

    return dict(col) if rec(0, 0) else None


def bfs_order(adj, r=0):
    order, seen = [r], {r}
    for v in order:
        for w in adj[v]:
            if w not in seen:
                seen.add(w)
                order.append(w)
    return order


def dfs_order(adj, r=0):
    order, seen, stack = [], set(), [r]
    while stack:
        v = stack.pop()
        if v in seen:
            continue
        seen.add(v)
        order.append(v)
        for w in reversed(adj[v]):
            if w not in seen:
                stack.append(w)
    return order


def thue_bt(adj, maxc=5, order=None, symbreak=True):
    order = order or bfs_order(adj)
    for k in range(1, maxc + 1):
        col = bt_colour(adj, k, order, symbreak)
        if col is not None:
            return k, col
    return None, None

# ----------------------------------------------------------------- trees

def canon_rooted(adj, v, p):
    return "(" + "".join(sorted(canon_rooted(adj, w, v) for w in adj[v] if w != p)) + ")"


def centres(adj):
    n = len(adj)
    deg = [len(a) for a in adj]
    removed = [False] * n
    leaves = [v for v in range(n) if deg[v] <= 1]
    rem = n
    while rem > 2:
        new = []
        for v in leaves:
            removed[v] = True
            rem -= 1
            for w in adj[v]:
                if not removed[w]:
                    deg[w] -= 1
                    if deg[w] == 1:
                        new.append(w)
        leaves = new
    return [v for v in range(n) if not removed[v]]


def canon(adj):
    return min(canon_rooted(adj, c, -1) for c in centres(adj))


def all_trees(N):
    """Non-isomorphic trees on n = 1..N vertices (leaf additions + canonical form)."""
    out = {1: [[[]]]}
    level = [[[]]]
    for n in range(2, N + 1):
        seen = {}
        for adj in level:
            for v in range(len(adj)):
                a = [list(x) for x in adj] + [[v]]
                a[v].append(len(adj))
                c = canon(a)
                if c not in seen:
                    seen[c] = a
        level = list(seen.values())
        out[n] = level
    return out


def complete_tree(depth, rootdeg=2):
    adj = [[]]
    frontier = [0]
    for _ in range(depth):
        nf = []
        for v in frontier:
            for _ in range(rootdeg if v == 0 else 2):
                w = len(adj)
                adj.append([v])
                adj[v].append(w)
                nf.append(w)
        frontier = nf
    return adj


def depths(adj, r):
    d = {r: 0}
    order = [r]
    for v in order:
        for w in adj[v]:
            if w not in d:
                d[w] = d[v] + 1
                order.append(w)
    return d

# ----------------------------------------------------------------- words

def ternary_squarefree(length):
    """A square-free word over {1,2,3} of the given length (backtracking; such words of every
    length exist by Thue's theorem)."""
    w = []

    def rec():
        if len(w) == length:
            return True
        for a in (1, 2, 3):
            w.append(a)
            # only squares that are suffixes need checking
            L = len(w)
            if not any(w[L - 2 * h:L - h] == w[L - h:] for h in range(1, L // 2 + 1)) and rec():
                return True
            w.pop()
        return False

    assert rec()
    return w


def insert_fourth(w):
    """Kuendgen-Pelsmajer: insert the letter 4 after every second letter."""
    u = []
    for i, a in enumerate(w):
        u.append(a)
        if i % 2 == 1:
            u.append(4)
    return u

# ----------------------------------------------------------------- main

def main():
    ok = True
    A000055 = [1, 1, 1, 2, 3, 6, 11, 23, 47, 106, 235, 551, 1301]
    N = 13 if "--n13" in sys.argv else 12

    print("== [A] K2 and P4 by plain enumeration of all colourings and all paths")
    K2 = [[1], [0]]
    P4 = [[1], [0, 2], [1, 3], [2]]
    for name, adj, want in (("K2", K2, 2), ("P4", P4, 3)):
        k, col = thue_bruteforce(adj)
        D = max(len(a) for a in adj)
        print(f"  {name}: Delta = {D}, pi = {k} (colouring {col}); 2*log2(Delta) = "
              f"{2 * math.log2(D):.3f}, 2*ln(Delta) = {2 * math.log(D):.3f}, "
              f"2*log10(Delta) = {2 * math.log10(D):.3f}")
        ok &= (k == want) and k > 2 * math.log2(D) and k > 2 * math.log(D)
    # the base threshold for P4: pi = 3 > 2 log_b 2 iff b > 4^(1/3)
    print(f"  P4 violates the bound for every base b > 4^(1/3) = {4 ** (1 / 3):.4f}; "
          f"K2 for every base b > 1")
    # the 16 2-colourings of P4: each has a square on a path
    two = [c for c in itertools.product(range(2), repeat=4) if is_nonrepetitive(P4, c)]
    print(f"  2-colourings of P4 that are nonrepetitive: {len(two)} (of 16)")
    ok &= (len(two) == 0)

    print(f"== [B] all trees with n <= {N} vertices")
    T = all_trees(N)
    maxpi = 0
    viol2 = viole = 0
    total = 0
    for n in range(1, N + 1):
        trees = T[n]
        cnt = {}
        for adj in trees:
            k, col = thue_bt(adj)
            assert is_nonrepetitive(adj, [col[v] for v in range(n)])  # full re-check
            cnt[k] = cnt.get(k, 0) + 1
            maxpi = max(maxpi, k)
            D = max((len(a) for a in adj), default=0)
            if D >= 1:
                if k > 2 * math.log2(D):
                    viol2 += 1
                if k > 2 * math.log(D):
                    viole += 1
        total += len(trees)
        ok &= (len(trees) == A000055[n - 1])
        print(f"  n = {n:2d}: {len(trees):4d} trees (A000055: {A000055[n - 1]}), "
              f"pi distribution {dict(sorted(cnt.items()))}")
    print(f"  max pi over all {total} trees: {maxpi}")
    print(f"  trees with Delta >= 1 violating pi <= 2 log2(Delta): {viol2}; "
          f"violating pi <= 2 ln(Delta): {viole}")
    ok &= (maxpi == 3)

    print("== [C] complete binary trees (root degree 2, all other internal vertices degree 3)")
    res = {}
    for h in range(1, 7):
        adj = complete_tree(h)
        k, col = thue_bt(adj)
        assert is_nonrepetitive(adj, [col[v] for v in range(len(adj))])  # full re-check
        res[h] = k
        D = max(len(a) for a in adj)
        print(f"  depth {h}: n = {len(adj):3d}, Delta = {D}, pi = {k}, "
              f"2*log2(Delta) = {2 * math.log2(D):.3f}")
    ok &= (res == {1: 2, 2: 3, 3: 3, 4: 3, 5: 3, 6: 4})
    adj6 = complete_tree(6)
    second = bt_colour(adj6, 3, dfs_order(adj6), symbreak=False)
    print(f"  second search (DFS order, no colour-symmetry breaking beyond the root): "
          f"3-colouring of depth 6 {'FOUND' if second else 'does not exist'}")
    ok &= (second is None)

    print("== [D] the pi(T) <= 4 construction (depth colouring by a square-free, "
          "distance-2 word on 4 letters)")
    w = ternary_squarefree(40)
    u = insert_fourth(w)
    sqf = not has_square(u)
    dist2 = all(len({u[i], u[i + 1], u[i + 2]}) == 3 for i in range(len(u) - 2))
    print(f"  w = {''.join(map(str, w))}")
    print(f"  u = {''.join(map(str, u))}  (square-free: {sqf}; any 3 consecutive distinct: {dist2})")
    ok &= sqf and dist2
    checked = 0
    for n in range(1, N + 1):
        for adj in T[n]:
            for r in range(n):
                d = depths(adj, r)
                col = [u[d[v]] for v in range(n)]
                if not is_nonrepetitive(adj, col):
                    ok = False
                    print("  FAILURE", adj, r)
                checked += 1
    print(f"  depth colouring nonrepetitive for all {checked} rooted trees with n <= {N}")
    for h in range(1, 9):
        adj = complete_tree(h)
        d = depths(adj, 0)
        good = is_nonrepetitive(adj, [u[d[v]] for v in range(len(adj))])
        ok &= good
        print(f"  complete binary tree depth {h} (n = {len(adj)}): depth colouring "
              f"nonrepetitive = {good}")

    print("== summary")
    print("  pi(K2) = 2 > 0 = 2 log 1;  pi(P4) = 3 > 2 log2 2 = 2 > 2 ln 2;")
    print("  complete binary tree of depth 6: pi = 4 > 2 log2 3 = 3.17;")
    print("  all trees checked have pi <= 4 (the theorem), so pi is bounded on trees.")
    print("ALL CHECKS PASSED" if ok else "SOME CHECK FAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
