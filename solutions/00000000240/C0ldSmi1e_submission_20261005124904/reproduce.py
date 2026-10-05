#!/usr/bin/env python3
"""Independent exact polytope checks for conjecture 00000000240.

Only Python's standard library is used.  All coordinates, supporting planes,
face centroids, determinants and volumes use fractions, never floating point.
These finite checks supplement, and do not replace, the Lean proof connecting
the bodies to Lebesgue volume and excluding all invertible linear images.
"""
from fractions import Fraction as Q
from itertools import combinations, product
from math import factorial
import json


def dot(a, b):
    return sum((x * y for x, y in zip(a, b)), Q(0))


def det(rows):
    """Exact determinant by fraction-preserving Gaussian elimination."""
    a = [list(map(Q, row)) for row in rows]
    n = len(a)
    assert all(len(row) == n for row in a)
    out = Q(1)
    for col in range(n):
        pivot = next((i for i in range(col, n) if a[i][col]), None)
        if pivot is None:
            return Q(0)
        if pivot != col:
            a[col], a[pivot] = a[pivot], a[col]
            out = -out
        q = a[col][col]
        out *= q
        for j in range(col, n):
            a[col][j] /= q
        for i in range(col + 1, n):
            q = a[i][col]
            for j in range(col, n):
                a[i][j] -= q * a[col][j]
    return out


def rank(rows, width):
    a = [list(map(Q, row)) for row in rows]
    assert all(len(row) == width for row in a)
    r = 0
    for col in range(width):
        pivot = next((i for i in range(r, len(a)) if a[i][col]), None)
        if pivot is None:
            continue
        a[r], a[pivot] = a[pivot], a[r]
        q = a[r][col]
        a[r] = [x / q for x in a[r]]
        for i in range(r + 1, len(a)):
            q = a[i][col]
            a[i] = [x - q * y for x, y in zip(a[i], a[r])]
        r += 1
    return r


def affine_dimension(vertices, face):
    points = [vertices[i] for i in sorted(face)]
    assert points
    return rank([[x - y for x, y in zip(p, points[0])]
                 for p in points[1:]], len(points[0]))


def hull_facets(vertices):
    """Enumerate every supporting plane through d affinely independent inputs.

    Each returned normal is normalized to normal.dot(x) <= 1.  The input must
    span R^d and have the origin strictly inside; both are checked here.
    """
    d = len(vertices[0])
    assert len(set(vertices)) == len(vertices)
    assert affine_dimension(vertices, frozenset(range(len(vertices)))) == d
    facets = {}
    for indices in combinations(range(len(vertices)), d):
        base = vertices[indices[0]]
        rows = [[x - y for x, y in zip(vertices[i], base)]
                for i in indices[1:]]
        normal = tuple((-1) ** j * det([r[:j] + r[j + 1:] for r in rows])
                       for j in range(d))
        if not any(normal):
            continue
        c = dot(normal, base)
        signed = [dot(normal, v) - c for v in vertices]
        if all(x <= 0 for x in signed):
            pass
        elif all(x >= 0 for x in signed):
            normal = tuple(-x for x in normal)
            c = -c
        else:
            continue
        assert c > 0, "origin must be strictly inside every supporting facet"
        normal = tuple(x / c for x in normal)
        face = frozenset(i for i, v in enumerate(vertices) if dot(normal, v) == 1)
        assert affine_dimension(vertices, face) == d - 1
        if face in facets:
            assert facets[face] == normal
        facets[face] = normal
    assert facets
    # Every claimed vertex is uniquely determined by independent active planes.
    for i in range(len(vertices)):
        assert rank([n for face, n in facets.items() if i in face], d) == d
    return facets


def exact_hull_volume(vertices):
    """Barycentric subdivision of the boundary, coned to the interior origin.

    The full face lattice is recovered by closing facets under intersection.
    A maximal proper-face flag determines one d-simplex with the origin.
    """
    facets = hull_facets(vertices)
    d = len(vertices[0])
    faces = set(facets)
    while True:
        added = {f & g for f in faces for g in facets if f & g} - faces
        if not added:
            break
        faces |= added
    by_dim = [[] for _ in range(d)]
    centers = {}
    for face in faces:
        dim = affine_dimension(vertices, face)
        assert 0 <= dim < d
        by_dim[dim].append(face)
        centers[face] = tuple(sum((vertices[i][j] for i in face), Q(0)) / len(face)
                              for j in range(d))
    for group in by_dim:
        group.sort(key=lambda x: tuple(sorted(x)))
    assert {next(iter(f)) for f in by_dim[0]} == set(range(len(vertices)))
    assert all(len(f) == 1 for f in by_dim[0])

    def flags(face, dimension):
        if dimension == 0:
            yield [face]
        else:
            for subface in by_dim[dimension - 1]:
                if subface < face:
                    for chain in flags(subface, dimension - 1):
                        yield chain + [face]

    result, simplices = Q(0), 0
    for facet in by_dim[-1]:
        for chain in flags(facet, d - 1):
            simplex_volume = abs(det([centers[f] for f in chain])) / factorial(d)
            assert simplex_volume > 0
            result += simplex_volume
            simplices += 1
    return result, {
        "dimension": d,
        "face_counts": [len(group) for group in by_dim],
        "boundary_flag_simplices": simplices,
        "volume": str(result),
    }, facets


def cross_vertices(d):
    return [tuple(Q(s if i == j else 0) for i in range(d))
            for j in range(d) for s in [-1, 1]]


def cube_vertices(d):
    return [tuple(map(Q, v)) for v in product([-1, 1], repeat=d)]


def main():
    # Independent reference shapes exercise simplicial and nonsimplicial facets.
    cube = cube_vertices(4)
    cross = cross_vertices(4)
    cv, cube_record, _ = exact_hull_volume(cube)
    xv, cross_record, _ = exact_hull_volume(cross)
    assert cv == 16 and xv == Q(2, 3)

    body = [(Q(s),) + v for s in [-1, 1] for v in cross_vertices(3)]
    assert all(abs(v[0]) == 1 and sum(map(abs, v[1:])) == 1 for v in body)
    assert set(tuple(-x for x in v) for v in body) == set(body)
    body_volume, body_record, body_facets = exact_hull_volume(body)
    polar = sorted(body_facets.values())
    expected_polar = [(Q(s), Q(0), Q(0), Q(0)) for s in [-1, 1]]
    expected_polar += [(Q(0),) + v for v in cube_vertices(3)]
    assert set(polar) == set(expected_polar)
    assert all(abs(v[0]) + max(map(abs, v[1:])) == 1 for v in polar)
    assert all(dot(v, w) <= 1 for v in body for w in polar)
    polar_volume, polar_record, polar_facets = exact_hull_volume(polar)
    assert set(polar_facets.values()) == set(body), "exact bipolar vertex check"

    # A second calculation uses sections, separately from the face triangulation.
    # octahedron3 = 8 standard orthant simplices, each volume 1/3!.
    body_sections = Q(2) * Q(8, factorial(3))
    # For |t|<=1 the polar section is a cube of side 2(1-|t|).
    # Integral of 16*(1-t)^3 over [0,1], evaluated coefficient by coefficient.
    polar_sections = Q(16) * (Q(1) - Q(3, 2) + Q(3, 3) - Q(1, 4))
    assert body_volume == body_sections == Q(8, 3)
    assert polar_volume == polar_sections == 4
    threshold = Q(4 ** 4, factorial(4))
    assert body_volume * polar_volume == threshold == Q(32, 3)
    assert len(body) == 12 and len(cube) == 16 and len(cross) == 8
    assert len(body) not in [len(cube), len(cross)]

    # A rational shear checks determinant normalization independently of symmetry.
    transform = [[Q(2), Q(1), Q(0), Q(0)],
                 [Q(0), Q(1), Q(1, 2), Q(0)],
                 [Q(0), Q(0), Q(1), Q(1)],
                 [Q(0), Q(0), Q(0), Q(1)]]
    transformed = [tuple(dot(row, v) for row in transform) for v in body]
    tv, transformed_record, _ = exact_hull_volume(transformed)
    assert det(transform) == 2 and tv == 2 * body_volume

    print(json.dumps({
        "result": "PASS",
        "arithmetic": "exact fractions; no floating-point decisions",
        "reference_cube4": cube_record,
        "reference_cross_polytope4": cross_record,
        "body": body_record,
        "polar": polar_record,
        "rational_shear": transformed_record,
        "mahler_product": str(body_volume * polar_volume),
        "stated_threshold": str(threshold),
        "independent_checks": [
            "full supporting-facet enumeration and extreme-vertex certificates",
            "exact primal/polar vertex-facet duality in both directions",
            "face-lattice barycentric determinant volumes",
            "separate exact section integrals",
            "cube and cross-polytope reference volumes",
            "nonsingular rational shear determinant scaling",
        ],
        "scope": "Computational corroboration only; Lean must prove the actual "
                 "body, polar, Lebesgue volumes and all-linear-image obstruction.",
    }, indent=2))


if __name__ == "__main__":
    main()
