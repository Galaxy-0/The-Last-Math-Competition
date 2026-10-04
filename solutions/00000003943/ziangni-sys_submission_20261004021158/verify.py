#!/usr/bin/env python3
"""Independent exhaustive verification; no external packages required."""
from itertools import combinations
import json


def edge(a, b):
    return (min(a, b), max(a, b))


def is_matching(m):
    vertices = [v for e in m for v in e]
    return len(vertices) == len(set(vertices))


def matchings(edges):
    def visit(i, m, used):
        if i == len(edges):
            yield frozenset(m)
            return
        yield from visit(i + 1, m, used)
        a, b = edges[i]
        if a not in used and b not in used:
            yield from visit(i + 1, m + [edges[i]], used | {a, b})
    yield from visit(0, [], set())


def augmenting_paths(n, graph, matching):
    used = {v for e in matching for v in e}
    def visit(path):
        if len(path) >= 2 and len(path) % 2 == 0 and path[-1] not in used:
            if path[0] < path[-1]:
                yield tuple(path)
        for v in range(n):
            if v in path:
                continue
            e = edge(path[-1], v)
            # The next edge is free at odd edge positions, matched at even positions.
            should_be_matched = len(path) % 2 == 0
            if e in graph and (e in matching) == should_be_matched:
                yield from visit(path + [v])
    for v in range(n):
        if v not in used:
            yield from visit([v])


def verify():
    counts = dict(graphs=0, matchings=0, augmenting_paths=0)
    for n in range(6):
        all_edges = list(combinations(range(n), 2))
        for bits in range(1 << len(all_edges)):
            graph = frozenset(e for i, e in enumerate(all_edges) if bits >> i & 1)
            counts['graphs'] += 1
            for matching in matchings(list(graph)):
                counts['matchings'] += 1
                assert is_matching(matching)
                assert 2 * len(matching) <= n
                for p in augmenting_paths(n, graph, matching):
                    path_edges = {edge(a, b) for a, b in zip(p, p[1:])}
                    free = {edge(p[i], p[i+1]) for i in range(0, len(p)-1, 2)}
                    old = {edge(p[i], p[i+1]) for i in range(1, len(p)-1, 2)}
                    assert old <= matching and free.isdisjoint(matching)
                    assert len(free) == len(old) + 1
                    toggled = matching ^ path_edges
                    assert toggled == (matching - old) | free
                    assert toggled <= graph and is_matching(toggled)
                    assert len(toggled) == len(matching) + 1
                    assert 2 * len(toggled) <= n
                    counts['augmenting_paths'] += 1
    for n in range(101):
        graph = frozenset((2*i, 2*i+1) for i in range(n//2))
        matching = frozenset()
        k = 0
        for e in graph:
            assert e not in matching
            matching = matching ^ {e}
            assert is_matching(matching)
            k += 1
        assert k == n//2 and matching == graph
    result = dict(status='PASS', exhaustive_orders='0 through 5',
                  tight_family_orders='0 through 100', **counts)
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    verify()
