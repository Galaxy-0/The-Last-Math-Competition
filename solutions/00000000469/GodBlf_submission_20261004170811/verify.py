"""Exact subset expansions; Python 3 standard library only."""
from itertools import combinations


def components(n, edges, selected):
    parent = list(range(n))

    def root(v):
        while parent[v] != v:
            v = parent[v]
        return v

    for i in selected:
        u, v = edges[i]
        parent[root(u)] = root(v)
    return len({root(v) for v in range(n)})


def polynomials(n, edges):
    m = len(edges)
    k = components(n, edges, range(m))
    flow, tension = {}, {}
    for size in range(m + 1):
        for selected in combinations(range(m), size):
            c = components(n, edges, selected)
            fexp, texp = size + c - n, c - k
            assert fexp >= 0 and texp >= 0
            flow[fexp] = flow.get(fexp, 0) + (-1) ** (m - size)
            tension[texp] = tension.get(texp, 0) + (-1) ** size
    return tuple(tuple(p.get(i, 0) for i in range(max(p) + 1))
                 for p in (flow, tension))


def main():
    triangle = polynomials(3, [(0, 1), (1, 2), (2, 0)])
    dual = polynomials(2, [(0, 1)] * 3)
    assert triangle == ((-1, 1), (2, -3, 1))
    assert dual == ((2, -3, 1), (-1, 1))
    assert triangle[0] == dual[1]
    assert triangle[1] == dual[0]
    assert all(sum(p) == 0 for pair in (triangle, dual) for p in pair)
    print("Coefficients in ascending powers:")
    print("C3 flow, tension:", triangle)
    print("C3* flow, tension:", dual)
    print("PASS: both duality identities; all four polynomials vanish at q=1.")


if __name__ == "__main__":
    main()
