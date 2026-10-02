#!/usr/bin/env python3
"""
Standalone recomputation for the disproof of TLMC conjecture 00000001226.

Conjecture (00000001226), verbatim:
  "Conjecture: The expected firefighter survival on 3-regular graphs is
   0.65n for an explicit constant (random firefighting expectation)."

Attack: the smallest 3-regular graph is K4 (n = 4).  Under the standard
firefighter process (fire breaks out at one vertex; each turn f vertices are
protected, then fire spreads to every unprotected neighbour of a burning
vertex; it ends when no unprotected vertex is adjacent to the fire) the whole
process on K4 is FORCED, for every strategy, random or not:

    f = 1:  exactly 1 vertex is saved  (0.25n)   -- 0.65n = 13/5 = 2.6
    f = 2:  exactly 2 vertices are saved (0.5n)
    f = 3:  exactly 3 vertices are saved (0.75n)

so the expected survival is a forced integer, never 13/5: the claimed law
fails on the very first member of the class, under every reading of the
undefined randomness.  The table below recomputes E[saved] exactly (rational
arithmetic, dynamic programming over all process states) on explicit cubic
graphs of every order n = 4, 6, 8, 10, under four readings:

  uniform_any    - each turn protect one vertex chosen uniformly at random
                   among ALL unburned, unprotected vertices;
  uniform_front  - same, but uniform among the fire front (unburned,
                   unprotected neighbours of the fire);
  optimal        - best possible strategy (upper bracket over ALL strategies);
  worst          - worst possible strategy (lower bracket).

It also verifies exhaustively (all labelled graphs, up to isomorphism) that
every cubic graph with n = 4 and n = 6 vertices refutes the claim, and runs a
Monte-Carlo on random cubic graphs at n up to 4096: under both canonical
random strategies the saved fraction stays far below 0.65 (and decreases).

Run:  python3 reproduce.py
Exit code 0 iff every check passes.
"""
import itertools
import random
import sys
from fractions import Fraction
from functools import lru_cache

FAILURES = []


def check(name, cond, detail=""):
    tag = "PASS" if cond else "FAIL"
    print(f"[{tag}] {name}" + (f"  ({detail})" if detail else ""))
    if not cond:
        FAILURES.append(name)


def claim(n):
    """0.65 n, the conjectured expected survival."""
    return Fraction(13, 20) * n


# ----------------------------------------------------------------------
# explicit 3-regular graphs
# ----------------------------------------------------------------------

def adj_from_edges(n, edges):
    adj = [set() for _ in range(n)]
    for a, b in edges:
        adj[a].add(b)
        adj[b].add(a)
    return adj


def is_cubic_connected(n, adj):
    if any(len(adj[v]) != 3 for v in range(n)):
        return False
    seen, st = {0}, [0]
    while st:
        v = st.pop()
        for w in adj[v]:
            if w not in seen:
                seen.add(w)
                st.append(w)
    return len(seen) == n


def graph_k4():
    return adj_from_edges(4, list(itertools.combinations(range(4), 2)))


def graph_k33():
    edges = [(a, b) for a in (0, 1, 2) for b in (3, 4, 5)]
    return adj_from_edges(6, edges)


def graph_prism():
    """triangular prism C3 x K2"""
    edges = []
    for s in (0, 1):
        for i in range(3):
            edges.append((3 * s + i, 3 * s + (i + 1) % 3))
    for i in range(3):
        edges.append((i, 3 + i))
    return adj_from_edges(6, edges)


def graph_cube():
    """cube Q3 = C4 x K2"""
    edges = []
    for s in (0, 1):
        for i in range(4):
            edges.append((4 * s + i, 4 * s + (i + 1) % 4))
    for i in range(4):
        edges.append((i, 4 + i))
    return adj_from_edges(8, edges)


def graph_wagner():
    """Wagner graph = Mobius ladder M8: C8 + antipodal chords"""
    edges = [(i, (i + 1) % 8) for i in range(8)]
    edges += [(i, (i + 4) % 8) for i in range(4)]
    return adj_from_edges(8, edges)


def graph_petersen():
    """Kneser(5,2): vertices = 2-subsets of {0..4}, adjacent iff disjoint."""
    pairs = list(itertools.combinations(range(5), 2))
    idx = {p: i for i, p in enumerate(pairs)}
    edges = []
    for a, b in itertools.combinations(pairs, 2):
        if not set(a) & set(b):
            edges.append((idx[a], idx[b]))
    return adj_from_edges(10, edges)


NAMED = [
    (4, "K4", graph_k4()),
    (6, "K3,3", graph_k33()),
    (6, "prism C3xK2", graph_prism()),
    (8, "cube Q3", graph_cube()),
    (8, "Wagner M8", graph_wagner()),
    (10, "Petersen", graph_petersen()),
]

for n, name, adj in NAMED:
    if not is_cubic_connected(n, adj):
        raise RuntimeError(f"{name} is not a connected cubic graph")

# ----------------------------------------------------------------------
# exhaustive enumeration of labelled connected cubic graphs (small n),
# deduplicated up to isomorphism by brute-force canonical labelling
# ----------------------------------------------------------------------


def connected_cubic_labelled(n):
    verts = list(range(n))
    for combo in itertools.combinations(list(itertools.combinations(verts, 2)),
                                        3 * n // 2):
        deg = [0] * n
        for a, b in combo:
            deg[a] += 1
            deg[b] += 1
        if deg != [3] * n:
            continue
        adj = adj_from_edges(n, combo)
        seen, st = {0}, [0]
        while st:
            v = st.pop()
            for w in adj[v]:
                if w not in seen:
                    seen.add(w)
                    st.append(w)
        if len(seen) == n:
            yield combo


def canon_edges(n, combo):
    best = None
    for perm in itertools.permutations(range(n)):
        rank = [0] * n
        for i, p in enumerate(perm):
            rank[p] = i
        code = tuple(sorted((min(rank[a], rank[b]), max(rank[a], rank[b]))
                            for a, b in combo))
        if best is None or code < best:
            best = code
    return best


def connected_cubic_classes(n):
    """unlabelled connected cubic graphs on n vertices, as adjacency lists."""
    seen, out = set(), []
    for combo in connected_cubic_labelled(n):
        c = canon_edges(n, combo)
        if c not in seen:
            seen.add(c)
            out.append(adj_from_edges(n, combo))
    return out


# ----------------------------------------------------------------------
# exact DP for the firefighter process
# ----------------------------------------------------------------------


def make_solver(n, adj, mode):
    """mode in {uniform_any, uniform_front, optimal, worst};

    returns V(burning, defended) = expected / extremal #saved from here.
    Rule: protect first, then every unprotected neighbour of the fire burns;
    the process ends when no unprotected vertex is adjacent to the fire.
    """
    full = frozenset(range(n))

    @lru_cache(maxsize=None)
    def V(burn, defend):
        front = set()
        for v in burn:
            front |= adj[v]
        avail = front - burn - defend
        if not avail:
            return n - len(burn)          # fire cannot spread any more
        pool_all = full - burn - defend
        if mode == "uniform_any":
            pool = pool_all
        elif mode == "uniform_front":
            pool = avail
        else:
            pool = pool_all
        if "uniform" in mode:
            tot = Fraction(0)
            for d in pool:
                tot += V(frozenset((burn | avail) - {d}),
                         frozenset(defend | {d}))
            return tot / len(pool)
        vals = [V(frozenset((burn | avail) - {d}), frozenset(defend | {d}))
                for d in pool_all]
        return max(vals) if mode == "optimal" else min(vals)

    return V


def profile(n, adj, mode):
    """(mean/min/max of V over the fire's start vertex)."""
    V = make_solver(n, adj, mode)
    es = [V(frozenset([v]), frozenset()) for v in range(n)]
    return sum(es) / n, min(es), max(es)


def forced_range_f(n, adj, f):
    """(min, max) of #saved over ALL strategies protecting f vertices per
    turn (defenders may pick any unburned, unprotected vertices each turn)."""

    @lru_cache(maxsize=None)
    def V(burn, defend):
        front = set()
        for v in burn:
            front |= adj[v]
        avail = front - burn - defend
        if not avail:
            return n - len(burn)
        pool = sorted(full - burn - defend)
        k = min(f, len(pool))
        vals = []
        for S in itertools.combinations(pool, k):
            vals.append(V(frozenset((burn | avail) - set(S)),
                          frozenset(defend | set(S))))
        return min(vals), max(vals)

    full = frozenset(range(n))
    lo = hi = None
    los, his = [], []
    for v in range(n):
        a, b = V(frozenset([v]), frozenset())
        los.append(a)
        his.append(b)
    return min(los), max(his)


# ----------------------------------------------------------------------
# C1: the forced K4 process (every strategy, f = 1, 2, 3)
# ----------------------------------------------------------------------
print("== C1: K4 (n=4), the process is forced; every strategy, f=1,2,3 ==")
k4 = graph_k4()
forced = {}
for f in (1, 2, 3):
    lo, hi = forced_range_f(4, k4, f)
    check(f"C1 K4, f={f}: outcome constant over all strategies/starts "
          f"(min={lo}, max={hi})", lo == hi)
    forced[f] = lo
check("C1 K4 f=1: exactly 1 vertex saved (= 0.25n)", forced[1] == 1)
check("C1 K4 f=2: exactly 2 vertices saved (= 0.5n)", forced[2] == 2)
check("C1 K4 f=3: exactly 3 vertices saved (= 0.75n)", forced[3] == 3)
for f in (1, 2, 3):
    check(f"C1 K4 f={f}: forced value {forced[f]} != 0.65n = 13/5",
          forced[f] != Fraction(13, 5),
          f"5*saved = 5*{forced[f]} = {5 * forced[f]} != 13")

# ----------------------------------------------------------------------
# C2: exact E[saved] on explicit cubic graphs, every order 4..10
# ----------------------------------------------------------------------
print()
print("== C2: exact E[saved] on explicit cubic graphs (f = 1) ==")
print(f"{'graph':>14} {'n':>3} {'0.65n':>7} {'uniform_any':>12} "
      f"{'uniform_front':>14} {'optimal':>8} {'worst':>6}")
rows = []
for n, name, adj in NAMED:
    prof = {m: profile(n, adj, m) for m in
            ("uniform_any", "uniform_front", "optimal", "worst")}
    ua, uf, op, wo = (prof[m][0] for m in
                      ("uniform_any", "uniform_front", "optimal", "worst"))
    print(f"{name:>14} {n:>3} {str(claim(n)):>7} {str(ua):>12} "
          f"{str(uf):>14} {str(op):>8} {str(wo):>6}")
    rows.append((n, name, prof))
    for m in ("uniform_any", "uniform_front", "optimal", "worst"):
        e, lo, hi = prof[m]
        check(f"C2 {name} n={n} mode={m}: E={e} (range {lo}..{hi}) "
              f"!= 0.65n = {claim(n)}",
              e != claim(n) and lo != claim(n) and hi != claim(n))
    check(f"C2 {name} n={n}: even OPTIMAL play (best start) < 0.65n",
          prof["optimal"][2] < claim(n))

# ----------------------------------------------------------------------
# C3: exhaustive at n = 4 and n = 6 -- EVERY cubic graph refutes
# ----------------------------------------------------------------------
print()
print("== C3: exhaustive over all cubic graphs, n = 4 and n = 6 ==")
for n, known in ((4, 1), (6, 2)):
    classes = connected_cubic_classes(n)
    check(f"C3 n={n}: enumeration finds the {known} known isomorphism "
          f"classes", len(classes) == known, f"found {len(classes)}")
    bad = 0
    for adj in classes:
        for m in ("uniform_any", "uniform_front", "optimal", "worst"):
            e, lo, hi = profile(n, adj, m)
            if e == claim(n) or lo == claim(n) or hi == claim(n):
                bad += 1
    check(f"C3 n={n}: all {known} classes, all 4 readings: "
          f"E[saved] != 0.65n", bad == 0)

# ----------------------------------------------------------------------
# C4: Monte-Carlo on random cubic graphs (scope: large n)
# ----------------------------------------------------------------------
print()
print("== C4: Monte-Carlo, random cubic graphs (f=1, random start) ==")
rng = random.Random(1226)


def random_cubic(n):
    while True:
        stubs = [v for v in range(n) for _ in range(3)]
        rng.shuffle(stubs)
        edges = set()
        ok = True
        for i in range(0, len(stubs), 2):
            a, b = stubs[i], stubs[i + 1]
            if a == b or (min(a, b), max(a, b)) in edges:
                ok = False
                break
            edges.add((min(a, b), max(a, b)))
        if not ok:
            continue
        adj = adj_from_edges(n, edges)
        if is_cubic_connected(n, adj):
            return adj


def simulate(adj, n, strat):
    burn = {rng.randrange(n)}
    defend = set()
    while True:
        front = set()
        for v in burn:
            front |= adj[v]
        avail = front - burn - defend
        if not avail:
            break
        pool = (set(range(n)) - burn - defend if strat == "uniform_any"
                else avail)
        d = rng.choice(sorted(pool))
        defend.add(d)
        burn |= (avail - {d})
    return n - len(burn)


for strat in ("uniform_any", "uniform_front"):
    for n, reps in ((256, 150), (1024, 60), (4096, 25)):
        tot = sum(simulate(random_cubic(n), n, strat) for _ in range(reps))
        frac = tot / reps / n
        print(f"   n={n:>5} {strat:>13}: mean saved fraction = {frac:.4f}"
              f"   (0.65 claimed)")
        check(f"C4 {strat} n={n}: saved fraction {frac:.4f} far below 0.65",
              frac < 0.5)

# ----------------------------------------------------------------------
print()
if FAILURES:
    print(f"RESULT: {len(FAILURES)} check(s) FAILED: {FAILURES}")
    sys.exit(1)
print("RESULT: all checks PASSED -- conjecture 00000001226 is FALSE "
      "(refuted on K4, n = 4, under every strategy and every f; "
      "no cubic graph of order n <= 10 tested reaches 0.65n under "
      "any reading).")
sys.exit(0)
