#!/usr/bin/env python3
"""Exact auxiliary certificate for conjecture 00000002161 only.

Python standard library only; no floating point, external CAS, Lean, or imports
from any submission. All polynomial coefficient lists are in ascending order.
The primary witness is fixed explicitly below, not selected by a search.
"""
from fractions import Fraction as Q
from itertools import combinations, permutations
import json


def require(condition, message):
    if not condition:
        raise ValueError(message)


def trim(p):
    p = list(map(Q, p))
    while len(p) > 1 and p[-1] == 0:
        p.pop()
    return p


def add(p, q):
    return trim([(p[i] if i < len(p) else 0) +
                 (q[i] if i < len(q) else 0)
                 for i in range(max(len(p), len(q)))])


def mul(p, q):
    r = [Q(0)] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        for j, b in enumerate(q):
            r[i + j] += a * b
    return trim(r)


def divrem(p, q):
    p, q = trim(p), trim(q)
    require(q != [0], "polynomial division by zero")
    quotient = [Q(0)] * max(1, len(p) - len(q) + 1)
    while p != [0] and len(p) >= len(q):
        k, a = len(p) - len(q), p[-1] / q[-1]
        quotient[k] += a
        p = add(p, [Q(0)] * k + [-a * x for x in q])
    return trim(quotient), p


def derivative(p):
    return trim([i * p[i] for i in range(1, len(p))] or [0])


def monic(p):
    return [x / p[-1] for x in p]


def gcd(p, q):
    while q != [0]:
        p, q = q, divrem(p, q)[1]
    return monic(p)


def sign(x):
    return (x > 0) - (x < 0)


def variations(signs):
    signs = [x for x in signs if x]
    return sum(x != y for x, y in zip(signs, signs[1:]))


def sturm(p):
    require(len(p) > 1, "Sturm input must have positive degree")
    require(len(gcd(p, derivative(p))) == 1, "Sturm input not squarefree")
    chain = [p, derivative(p)]
    while len(chain[-1]) > 1:
        r = [-x for x in divrem(chain[-2], chain[-1])[1]]
        require(r != [0], "unexpected zero remainder")
        chain.append(r)
    signs = {
        "negative_infinity": [sign(s[-1]) * (-1) ** (len(s) - 1) for s in chain],
        "zero": [sign(s[0]) for s in chain],
        "positive_infinity": [sign(s[-1]) for s in chain],
    }
    v = {k: variations(s) for k, s in signs.items()}
    require(p[0] != 0, "zero roots must be removed before endpoint counting")
    return {
        "chain": chain, "signs": signs, "variations": v,
        "negative_distinct_roots": v["negative_infinity"] - v["zero"],
        "positive_distinct_roots": v["zero"] - v["positive_infinity"],
    }


def characteristic(matrix):
    """Leibniz determinant of xI-A; no spectral formulas are assumed."""
    n = len(matrix)
    determinant = [Q(0)]
    nonzero_terms = []
    for permutation in permutations(range(n)):
        inversions = sum(permutation[i] > permutation[j]
                         for i in range(n) for j in range(i + 1, n))
        term = [Q((-1) ** inversions)]
        for i, j in enumerate(permutation):
            term = mul(term, [-matrix[i][j], 1] if i == j else [-matrix[i][j]])
        determinant = add(determinant, term)
        if term != [0]:
            nonzero_terms.append({"permutation": permutation, "polynomial": term})
    return determinant, nonzero_terms


def inertia(poly):
    """Multiplicity-aware root count by repeated squarefree layers.

    gcd(p,p') reduces each nonzero root multiplicity by one; p/gcd is
    squarefree. Count each layer with Sturm, then continue with the gcd.
    For a real symmetric matrix these real-root counts are its inertia.
    """
    p = poly[:]
    zero = 0
    while p[0] == 0:
        zero += 1
        p = p[1:]
    positive = negative = 0
    layers = []
    while len(p) > 1:
        g = gcd(p, derivative(p))
        squarefree, remainder = divrem(p, g)
        require(remainder == [0], "gcd does not divide polynomial")
        counts = sturm(squarefree)
        positive += counts["positive_distinct_roots"]
        negative += counts["negative_distinct_roots"]
        layers.append(counts)
        p = g
    require(positive + negative + zero == len(poly) - 1,
            "not all roots were certified real")
    return {"positive": positive, "negative": negative, "zero": zero,
            "squarefree_layers": layers}


def graph(n, edges):
    require(n > 0, "graph must have vertices")
    require(len({(u, v) for u, v, s in edges}) == len(edges), "duplicate edge")
    require(all(0 <= u < v < n and s in (-1, 1) for u, v, s in edges),
            "invalid signed simple edge")
    adjacency = [[0] * n for _ in range(n)]
    for u, v, s in edges:
        adjacency[u][v] = adjacency[v][u] = s
    require(all(adjacency[i][j] == adjacency[j][i] for i in range(n) for j in range(n)),
            "adjacency not symmetric")
    require(all(adjacency[i][i] == 0 for i in range(n)), "nonzero diagonal")
    subsets = []
    for mask in range(1 << n):
        subset = [v for v in range(n) if mask & (1 << v)]
        conflicts = [[u, v] for u, v, s in edges if u in subset and v in subset]
        subsets.append({"vertices": subset, "independent": not conflicts,
                        "contained_edges": conflicts})
    independent = [x["vertices"] for x in subsets if x["independent"]]
    alpha = max(map(len, independent))
    reached = {0}
    while True:
        extended = reached | {v for u in reached for v in range(n) if adjacency[u][v]}
        if extended == reached:
            break
        reached = extended
    missing = [[i, j] for i, j in combinations(range(n), 2) if not adjacency[i][j]]
    polynomial, determinant_terms = characteristic(adjacency)
    return {"vertices": list(range(n)), "signed_edges": edges,
            "adjacency_matrix": adjacency, "all_subsets": subsets,
            "independent_sets": independent, "independence_number": alpha,
            "maximum_independent_sets": [s for s in independent if len(s) == alpha],
            "connected": len(reached) == n, "reachable_from_zero": sorted(reached),
            "complete": not missing, "missing_edges": missing,
            "characteristic_polynomial": polynomial,
            "nonzero_determinant_terms": determinant_terms,
            "inertia": inertia(polynomial)}


def cycles(permutation):
    require(set(permutation) == set(permutation.values()), "not a permutation")
    left, result = set(permutation), []
    while left:
        start, cycle = min(left), []
        current = start
        while current in left:
            left.remove(current)
            cycle.append(current)
            current = permutation[current]
        require(current == start, "cycle does not close at its start")
        result.append(cycle)
    return result


def topology(n, edges, rotations):
    """Construct oriented face polygons, glue edges, and check all local links.

    At each polygon corner a link arc joins its incoming and outgoing flags.
    Edge gluings pair those flag ends. Each connected 2-regular link is a
    circle, so each quotient vertex has a disk neighborhood.
    """
    darts = sorted([(u, v) for u, v, _ in edges] + [(v, u) for u, v, _ in edges])
    require(set(rotations) == set(range(n)), "missing vertex rotation")
    alpha = {d: (d[1], d[0]) for d in darts}
    sigma = {}
    for vertex, rotation in rotations.items():
        expected = {d for d in darts if d[0] == vertex}
        require(len(rotation) > 0 and len(rotation) == len(set(rotation)),
                "empty or duplicate local dart")
        require(set(rotation) == expected, "local rotation is not exactly its vertex star")
        for i, d in enumerate(rotation):
            sigma[d] = rotation[(i + 1) % len(rotation)]
    require(all(alpha[alpha[d]] == d and alpha[d] != d for d in darts),
            "edge reversal is not a fixed-point-free involution")
    vertex_cycles, edge_cycles = cycles(sigma), cycles(alpha)
    require(len(vertex_cycles) == n and len(edge_cycles) == len(edges), "wrong cells")
    phi = {d: sigma[alpha[d]] for d in darts}
    faces = cycles(phi)
    require(all(d[1] == phi[d][0] for d in darts), "face walk is not incident")
    orbit = {darts[0]}
    while True:
        extended = orbit | {f[d] for d in orbit for f in (alpha, sigma)}
        if extended == orbit:
            break
        orbit = extended
    require(orbit == set(darts), "map not connected")
    corners = [(f, i) for f, face in enumerate(faces) for i in range(len(face))]
    locations = {d: (f, i) for f, face in enumerate(faces) for i, d in enumerate(face)}
    successor = {(f, i): (f, (i + 1) % len(faces[f])) for f, i in corners}
    labels = {(f, i): faces[f][i][0] for f, i in corners}
    parent = {c: c for c in corners}

    def find(c):
        while parent[c] != c:
            c = parent[c]
        return c

    def union(c, d):
        parent[find(c)] = find(d)

    flags = [(f, i, side) for f, i in corners for side in ("in", "out")]
    link = {flag: [] for flag in flags}
    link_edges = []

    def link_edge(a, b, kind):
        link[a].append(b)
        link[b].append(a)
        link_edges.append({"ends": [a, b], "kind": kind})

    for f, i in corners:
        link_edge((f, i, "in"), (f, i, "out"), "corner arc")
    gluings = []
    for a, b in edge_cycles:
        c, d = locations[a], locations[b]
        cnext, dnext = successor[c], successor[d]
        require(labels[c] == labels[dnext] and labels[cnext] == labels[d],
                "paired sides do not have opposite endpoints")
        union(c, dnext)
        union(cnext, d)
        link_edge((*c, "out"), (*dnext, "in"), "edge gluing")
        link_edge((*cnext, "in"), (*d, "out"), "edge gluing")
        gluings.append({"darts": [a, b], "polygon_sides": [c, d],
                        "identified_corners": [[c, dnext], [cnext, d]]})
    classes = {}
    for c in corners:
        classes.setdefault(find(c), []).append(c)
    quotient_classes = sorted(classes.values())
    require(len(quotient_classes) == n, "wrong number of quotient vertices")
    require(all(find(c) == find(d) if labels[c] == labels[d] else find(c) != find(d)
                for c in corners for d in corners), "quotient vertices differ from graph")
    require(all(len(link[f]) == 2 for f in flags), "vertex link not 2-regular")
    remaining, link_components = set(flags), []
    while remaining:
        component, pending = set(), [min(remaining)]
        while pending:
            flag = pending.pop()
            if flag not in component:
                component.add(flag)
                pending.extend(link[flag])
        remaining -= component
        component_labels = {labels[f[:2]] for f in component}
        require(len(component_labels) == 1, "link joins distinct graph vertices")
        link_components.append({"vertex": next(iter(component_labels)),
                                "flags": sorted(component),
                                "degrees": [len(link[f]) for f in sorted(component)]})
    require(len(link_components) == n and
            {x["vertex"] for x in link_components} == set(range(n)),
            "some quotient vertex has multiple link circles")
    chi = n - len(edges) + len(faces)
    require((2 - chi) % 2 == 0 and chi <= 2, "invalid orientable Euler characteristic")
    return {"darts": darts, "permutation_table":
            [{"dart": d, "alpha": alpha[d], "sigma": sigma[d], "phi": phi[d]} for d in darts],
            "vertex_cycles": vertex_cycles, "edge_cycles": edge_cycles,
            "face_cycles": faces, "transitive": True, "edge_gluings": gluings,
            "quotient_vertex_corner_classes": quotient_classes,
            "link_edges": link_edges, "vertex_link_components": link_components,
            "all_links_are_single_circles": True,
            "cell_counts_V_E_F": [n, len(edges), len(faces)],
            "euler_characteristic": chi, "orientable_genus": (2 - chi) // 2,
            "euler_genus": 2 - chi}


def cross(a, b):
    return a[0] * b[1] - a[1] * b[0]


def subtract(a, b):
    return (a[0] - b[0], a[1] - b[1])


def on_segment(point, a, b):
    return cross(subtract(point, a), subtract(b, a)) == 0 and all(
        min(a[i], b[i]) <= point[i] <= max(a[i], b[i]) for i in (0, 1))


def segment_intersection(a, b, c, d):
    r, s, ca = subtract(b, a), subtract(d, c), subtract(c, a)
    denominator = cross(r, s)
    if denominator:
        t, u = Q(cross(ca, s), denominator), Q(cross(ca, r), denominator)
        return [(a[0] + t * r[0], a[1] + t * r[1])] if 0 <= t <= 1 and 0 <= u <= 1 else []
    if cross(ca, r):
        return []
    # Collinear: >=2 distinct endpoints in the intersection means overlap.
    return sorted({p for p in (a, b, c, d) if on_segment(p, a, b) and on_segment(p, c, d)})


def drawing(n, edges, points):
    require(set(points) == set(range(n)) and len(set(points.values())) == n,
            "vertices not distinct")
    nonincident_checks, intersections = [], []
    for u, v, _ in edges:
        require(points[u] != points[v], "degenerate segment")
        for w in range(n):
            if w not in (u, v):
                lies = on_segment(points[w], points[u], points[v])
                require(not lies, "nonincident vertex lies on an edge")
                nonincident_checks.append({"vertex": w, "edge": [u, v], "on_edge": lies})
    for first, second in combinations(edges, 2):
        u, v, _ = first
        w, z, _ = second
        actual = segment_intersection(points[u], points[v], points[w], points[z])
        expected = sorted(points[a] for a in set((u, v)) & set((w, z)))
        require(actual == expected, "edges intersect beyond shared endpoint")
        intersections.append({"edges": [[u, v], [w, z]], "intersection": actual})
    return {"coordinates": points, "nonincident_vertex_checks": nonincident_checks,
            "edge_pair_intersections": intersections, "crossing_free": True}


def expect_rejection(operation):
    try:
        operation()
    except ValueError as error:
        return str(error)
    raise ValueError("invalid certificate was accepted")


def main():
    edges = [(0, 1, 1), (1, 2, 1), (2, 3, 1)]
    rotations = {0: [(0, 1)], 1: [(1, 0), (1, 2)],
                 2: [(2, 1), (2, 3)], 3: [(3, 2)]}
    primary = graph(4, edges)
    primary["rotation_system_embedding"] = topology(4, edges, rotations)
    primary["straight_line_embedding"] = drawing(4, edges, {i: (i, 0) for i in range(4)})
    require(primary["independence_number"] == primary["inertia"]["positive"] == 2,
            "candidate does not attain stated equality")
    require(primary["connected"] and not primary["complete"], "candidate inadmissible")
    require(primary["rotation_system_embedding"]["orientable_genus"] == 0, "not genus zero")
    boundaries = []
    for label, n, e, expected in [
        ("K2: equality but excluded because complete", 2, [(0, 1, 1)], (1, 1, 1, 0)),
        ("P3: stated universal inequality is false", 3, [(0, 1, 1), (1, 2, 1)], (2, 1, 1, 1)),
        ("K3: negative eigenvalue has multiplicity two", 3,
         [(0, 1, 1), (0, 2, 1), (1, 2, 1)], (1, 1, 2, 0)),
    ]:
        result = graph(n, e)
        actual = (result["independence_number"], result["inertia"]["positive"],
                  result["inertia"]["negative"], result["inertia"]["zero"])
        require(actual == expected, "boundary case mismatch")
        boundaries.append({"case": label, "alpha_pos_neg_zero": actual,
                           "complete": result["complete"],
                           "characteristic_polynomial": result["characteristic_polynomial"],
                           "inertia_certificate": result["inertia"]})
    malformed = dict(rotations)
    malformed[1] = [(1, 0)]
    rejections = {
        "missing_dart_in_rotation": expect_rejection(lambda: topology(4, edges, malformed)),
        "crossing_square": expect_rejection(lambda: drawing(4,
            [(0, 1, 1), (1, 2, 1), (2, 3, 1), (0, 3, 1)],
            {0: (0, 0), 1: (1, 1), 2: (0, 1), 3: (1, 0)})),
        "vertex_inside_nonincident_edge": expect_rejection(lambda: drawing(4, edges,
            {0: (0, 0), 1: (3, 0), 2: (1, 0), 3: (4, 0)})),
    }
    print(json.dumps({"conjecture": "00000002161", "arithmetic": "exact rational",
                      "polynomial_coefficient_order": "constant to highest degree",
                      "primary_witness": primary, "boundary_checks": boundaries,
                      "invalid_certificate_rejections": rejections,
                      "result": "PASS: P4 is connected, noncomplete, alpha=i_+=2, minimum genus=0"},
                     indent=2, default=lambda x: str(x)))


if __name__ == "__main__":
    main()
