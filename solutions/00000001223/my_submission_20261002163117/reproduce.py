#!/usr/bin/env python3
"""
Reproduction script for the refutation of TLMC conjecture 00000001223.

Conjecture (verbatim): "Definition: The surround cop number is the least number
of cops needed to surround rather than capture. Conjecture: The surround cop
number of a cubic graph is two; and tightness of the surround constant is
attained by the Petersen graph."

The surrounding cops-and-robbers game (Burgess, Cameron, Clarke, Danziger,
Finbow, Jones, Pike, "Cops that surround a robber", arXiv:1910.14200;
Discrete Applied Mathematics, doi:10.1016/j.dam.2020.06.019): k cops occupy
vertices of G, then the robber
occupies a vertex; in each round every cop may stay or move along an edge
(cops never occupy the robber's vertex), then the robber must move along an
edge to an unoccupied vertex.  The cops WIN as soon as they occupy every
neighbour of the robber's current vertex; the robber wins if that never
happens.  sigma(G) is the least k for which the cops have a winning strategy.

Refutation summary:
  * every cubic graph is 3-regular, so the robber always stands on a vertex
    with exactly three DISTINCT neighbours;
  * two cops occupy at most two vertices, so the surround condition can never
    hold -- at time zero, hence at no moment of any play (rule-independent);
  * hence sigma(G) >= 3 for EVERY cubic graph, and the value 2 is attained by
    no cubic graph at all;
  * K4 is the smallest witness: sigma(K4) = 3 exactly (three cops placed on
    all vertices except the robber's surround it at time zero).

Standard library only.  Run:  python3 reproduce.py
Exit code 0 iff every check passes.
"""

import itertools
import sys

FAILURES = []


def check(name, ok, detail=""):
    print(f"[{'PASS' if ok else 'FAIL'}] {name}" + (f"  {detail}" if detail else ""))
    if not ok:
        FAILURES.append(name)


# --------------------------------------------------------------------------
# The five cubic graphs of the attack note
# --------------------------------------------------------------------------

def make_K4():
    adj = {v: set() for v in range(4)}
    for v in range(4):
        for u in range(4):
            if u != v:
                adj[v].add(u)
    return adj


def make_Petersen():
    # outer cycle 0..4, inner star 5..9 (5+j ~ 5+(j+2) mod 5), spokes i ~ 5+i
    adj = {v: set() for v in range(10)}

    def E(a, b):
        adj[a].add(b)
        adj[b].add(a)

    for i in range(5):
        E(i, (i + 1) % 5)
        E(i, i + 5)
    for j in range(5):
        E(5 + j, 5 + (j + 2) % 5)
    return adj


def make_Q3():
    adj = {v: set() for v in range(8)}
    for v in range(8):
        for b in range(3):
            adj[v].add(v ^ (1 << b))
    return adj


def make_K33():
    adj = {v: set() for v in range(6)}
    for a in range(3):
        for b in range(3, 6):
            adj[a].add(b)
            adj[b].add(a)
    return adj


def make_prism():
    adj = {v: set() for v in range(6)}

    def E(a, b):
        adj[a].add(b)
        adj[b].add(a)

    E(0, 1); E(1, 2); E(2, 0)
    E(3, 4); E(4, 5); E(5, 3)
    for i in range(3):
        E(i, i + 3)
    return adj


GRAPHS = {
    "K4": make_K4(),
    "Petersen": make_Petersen(),
    "Q3": make_Q3(),
    "K3,3": make_K33(),
    "prism": make_prism(),
}


def surrounded(adj, cops, v):
    return all(u in cops for u in adj[v])


# --------------------------------------------------------------------------
# 1. Sanity: all five graphs are simple, cubic, symmetric
# --------------------------------------------------------------------------

print("== sanity checks ==")
for name, adj in GRAPHS.items():
    n = len(adj)
    cubic = all(len(adj[v]) == 3 for v in adj)
    distinct = all(len(adj[v]) == len(set(adj[v])) for v in adj)
    symmetric = all(v in adj[u] for v in adj for u in adj[v])
    check(f"{name}: simple cubic with distinct neighbours", cubic and distinct,
          f"n={n}")
    check(f"{name}: adjacency symmetric", symmetric)

# --------------------------------------------------------------------------
# 2. Exhaustive invariant: no 2-cop placement ever surrounds any robber vertex
# --------------------------------------------------------------------------

print()
print("== exhaustive 2-cop impossibility (all placements, incl. stacked cops) ==")
for name, adj in GRAPHS.items():
    n = len(adj)
    configs = 0
    bad = []
    for c1 in range(n):
        for c2 in range(n):
            for v in range(n):
                configs += 1
                if surrounded(adj, {c1, c2}, v):
                    bad.append((c1, c2, v))
    check(f"{name}: no two cops surround any vertex", not bad,
          f"{configs} configurations checked, {len(bad)} violations")

# --------------------------------------------------------------------------
# 3. K4: three cops suffice (witness placement surrounds at time zero)
# --------------------------------------------------------------------------

print()
print("== K4 upper bound ==")
adj = GRAPHS["K4"]
ok = all(surrounded(adj, set(range(4)) - {v}, v) for v in range(4))
check("K4: cops on V\\{v} surround a robber at v, for every v", ok)
check("K4: sigma(K4) = 3 exactly", ok)

# --------------------------------------------------------------------------
# 4. Full game search: sigma for all five graphs (retrograde reachability)
# --------------------------------------------------------------------------

print()
print("== retrograde game search (standard rules, see module docstring) ==")


def cop_moves(adj, c, r, k):
    per = []
    for x in c:
        choices = [x] + sorted(adj[x] - {r})
        per.append(choices)
    out = set()
    for combo in itertools.product(*per):
        if len(set(combo)) == k:  # cops stay pairwise distinct
            out.add(tuple(sorted(combo)))
    return out


def sigma(name):
    adj = GRAPHS[name]
    V = sorted(adj)
    for k in range(1, 6):
        places = list(itertools.combinations(V, k))
        copwin = set()
        changed = True
        while changed:
            changed = False
            for c in places:
                cs = frozenset(c)
                for r in V:
                    if r in cs or (cs, r) in copwin:
                        continue
                    if surrounded(adj, cs, r):
                        copwin.add((cs, r))
                        changed = True
                        continue
                    win = False
                    for c2 in cop_moves(adj, cs, r, k):
                        c2s = frozenset(c2)
                        if surrounded(adj, c2s, r):
                            win = True
                            break
                        legal = [u for u in adj[r] if u not in c2s]
                        if legal and all((c2s, u) in copwin for u in legal):
                            win = True
                            break
                    if win:
                        copwin.add((cs, r))
                        changed = True
        # cops choose their initial placement first, then the robber picks a vertex
        cops_win = any(
            all((frozenset(c), r) in copwin for r in V if r not in c)
            for c in places
        )
        print(f"    {name}: k={k} -> cops win: {cops_win} "
              f"({len(copwin)} configurations won)")
        if cops_win:
            return k, len(copwin)
    return None, 0


for name in GRAPHS:
    s, won = sigma(name)
    check(f"{name}: sigma = 3 (game search)", s == 3, f"won states: {won}")

# --------------------------------------------------------------------------
print()
if FAILURES:
    print("RESULT: FAILURES:", FAILURES)
    sys.exit(1)
print("RESULT: ALL CHECKS PASS")
print()
print("Conjecture 00000001223 is FALSE: the surround cop number of a cubic")
print("graph is never two -- sigma(G) >= 3 for every cubic graph G (K4,")
print("Petersen, Q3, K3,3 and the triangular prism all have sigma = 3), so")
print("the value 2 is attained by no cubic graph at all.")
sys.exit(0)
