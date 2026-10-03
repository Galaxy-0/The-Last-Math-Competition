#!/usr/bin/env python3
"""Independent verification for the disproof of conjecture 00000002732."""
import sys
from itertools import product

def main():
    E = set()
    for i in range(5):
        E.add(tuple(sorted((i, (i + 1) % 5))))
        E.add(tuple(sorted((i, 5 + (i + 1) % 5))))
        E.add(tuple(sorted((i, 5 + (i - 1) % 5))))
        E.add(tuple(sorted((5 + i, 10))))
    E = sorted(E)
    Eset = set(E)
    print(f"Groetzsch graph: 11 vertices, {len(E)} edges")
    # triangle-free
    tris = []
    for a, b in E:
        for c in range(11):
            if c in (a, b):
                continue
            if (min(a, c), max(a, c)) in Eset and (min(b, c), max(b, c)) in Eset:
                tris.append((a, b, c))
    print(f"triangles: {tris}")
    assert not tris
    # exhaustive 3-coloring
    found3 = None
    for colors in product(range(3), repeat=11):
        if all(colors[a] != colors[b] for a, b in E):
            found3 = colors
            break
    print(f"3-coloring exists? {found3 is not None}")
    assert found3 is None
    # 4-coloring
    found4 = None
    for colors in product(range(4), repeat=11):
        if all(colors[a] != colors[b] for a, b in E):
            found4 = colors
            break
    print(f"4-coloring: {found4}")
    assert found4 == (0, 1, 0, 1, 2, 0, 1, 0, 1, 2, 3)
    # links 0-dimensional <=> triangle-free; bound
    print("links are 0-dimensional (chi=1); conjectured bound 2+1 = 3 < 4 = chi(Delta)")
    print("ALL CHECKS PASS — conjecture refuted")
    return 0

if __name__ == "__main__":
    sys.exit(main())
