#!/usr/bin/env python3
"""
Standalone reproduction of the disproof of TLMC conjecture 00000000544
(single-edge forest K2 attack). No third-party dependencies.

Run:  python3 reproduce.py

Conjecture: for every graph G without isolated vertices,
    |Graver(I_{A_G})| <= sum_{H subseteq G, H forest} 2^{|V(H)|},
    with EQUALITY attained on forests.

Attack: G = K_2. A_{K_2} = [[1],[1]] (2x1 unoriented incidence matrix).
The lattice ker_Z(A) = {u in Z : u = 0} = {0} has no nonzero (irreducible)
elements, so |Graver| = 0, while the RHS >= 2^2 = 4 because H = K_2 itself is a
spanning forest. Equality fails.
"""

import itertools

# ---------------------------------------------------------------- toric data
# Unoriented incidence matrix of K2: 2 vertices, 1 edge, column (1, 1)^T.
A = [[1], [1]]
NROWS, NCOLS = len(A), len(A[0])


def mat_vec(u):
    """A * u for u in Z^NCOLS."""
    return [sum(A[i][j] * u[j] for j in range(NCOLS)) for i in range(NROWS)]


def lattice_in_box(box):
    """All lattice points u in [-box, box]^NCOLS with A u = 0."""
    return [
        u
        for u in itertools.product(range(-box, box + 1), repeat=NCOLS)
        if all(entry == 0 for entry in mat_vec(u))
    ]


def is_irreducible(u, lattice):
    """u in lattice is Graver-irreducible if it has no decomposition
    u = v + w with v, w nonzero lattice elements, sign-compatible with u,
    and |v_j| <= |u_j| componentwise (a 'proper' sign-consistent split)."""
    for v in lattice:
        if v == (0,) * NCOLS:
            continue
        if not all((v[j] == 0) or (v[j] > 0) == (u[j] > 0) for j in range(NCOLS)):
            continue
        if not all(abs(v[j]) <= abs(u[j]) for j in range(NCOLS)):
            continue
        w = tuple(u[j] - v[j] for j in range(NCOLS))
        if w == (0,) * NCOLS or w not in lattice:
            continue
        if not all((w[j] == 0) or (w[j] > 0) == (u[j] > 0) for j in range(NCOLS)):
            continue
        return False  # found a proper decomposition
    return True


def graver_basis(box):
    lattice = lattice_in_box(box)
    nonzero = [u for u in lattice if u != (0,) * NCOLS]
    return [u for u in nonzero if is_irreducible(u, lattice)]


# --------------------------------------------------------------- graph side
def is_forest(n_vertices, edges):
    """Union-find cycle check."""
    parent = list(range(n_vertices))

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    for a, b in edges:
        ra, rb = find(a), find(b)
        if ra == rb:
            return False
        parent[ra] = rb
    return True


def rhs_spanning_forests(n_vertices, all_edges):
    """sum of 2^{|V(H)|} over all spanning forest subgraphs H (same vertex set)."""
    total = 0
    for mask in range(2 ** len(all_edges)):
        edges = [all_edges[j] for j in range(len(all_edges)) if (mask >> j) & 1]
        if is_forest(n_vertices, edges):
            total += 2 ** n_vertices
    return total


def rhs_all_subgraphs(all_edges):
    """sum over ALL forest subgraphs (every vertex subset), the most generous reading."""
    total = 0
    n_edges = len(all_edges)
    for n_vertices in range(len({v for e in all_edges for v in e}), -1, -1):
        if n_vertices == 0:
            total += 2 ** 0  # empty subgraph
            continue
        for mask in range(2 ** n_edges):
            edges = [all_edges[j] for j in range(n_edges) if (mask >> j) & 1]
            if n_vertices < 2 and edges:
                continue
            if is_forest(n_vertices, edges):
                # count injections of the vertex set into the endpoints: C(2, nv) choices
                from math import comb
                total += comb(2, n_vertices) * 2 ** n_vertices
    return total


# --------------------------------------------------------------------- main
def main():
    box = 100
    lattice = lattice_in_box(box)

    # sanity: the lattice condition A u = 0 reads (u0, u0) = (0, 0), i.e. u0 = 0.
    assert lattice == [(0,)], f"unexpected lattice members: {lattice}"
    print(f"lattice ker_Z(A_K2) in [-{box},{box}]^{NCOLS}: {lattice}   (exactly {{0}})")

    graver = graver_basis(box)
    print(f"Graver basis of I_(A_K2): {graver}")
    n_graver = len(graver)
    print(f"|Graver(I_(A_K2))| = {n_graver}")

    # K2: two vertices, one edge
    edges_k2 = [(0, 1)]
    rhs_span = rhs_spanning_forests(2, edges_k2)
    rhs_all = rhs_all_subgraphs(edges_k2)
    print(f"RHS over spanning forest subgraphs of K2 = 2^2 + 2^2 = {rhs_span}")
    print(f"RHS over all forest subgraphs of K2 (generous reading) = {rhs_all}")
    rhs_lower_bound = 2 ** 2  # the single summand H = G = K2 itself
    print(f"universal lower bound (summand H = K2 alone): {rhs_lower_bound}")

    print()
    print(f"equality on forests:  |Graver| ({n_graver}) == RHS ?")
    print(f"  -> {n_graver} != {rhs_lower_bound} <= RHS  (RHS = {rhs_span} spanning, {rhs_all} all)")
    assert n_graver < rhs_lower_bound <= rhs_span
    print()
    print("CONCLUSION: the equality-on-forests clause of conjecture 00000000544 FAILS")
    print("            on the single-edge forest K2.  Conjecture FALSIFIED.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
