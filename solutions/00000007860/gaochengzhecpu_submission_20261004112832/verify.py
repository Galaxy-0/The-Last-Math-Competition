"""Auxiliary exact check of the actual singleton graph and its uniform orders.
The Lean proof is authoritative. This script checks only the exhibited witness;
it does not infer a statement about all graph sizes from bounded searches.
"""
import itertools
import json
from fractions import Fraction


def greedy_coloring(n, edges, order):
    assert sorted(order) == list(range(n))
    colors = {}
    trace = []
    for v in order:
        forbidden = {colors[u] for u in colors if frozenset((u, v)) in edges}
        color = 0
        while color in forbidden:
            color += 1
        colors[v] = color
        trace.append({"vertex": v, "forbidden": sorted(forbidden), "color": color})
    assert all(colors[u] != colors[v] for u, v in map(tuple, edges))
    return len(set(colors.values())), trace


def chromatic_number(n, edges):
    for k in range(n + 1):
        for colors in itertools.product(range(k), repeat=n):
            if all(colors[u] != colors[v] for u, v in map(tuple, edges)):
                return k
    raise AssertionError("finite graph has no coloring")


def main():
    n, edges = 1, set()
    orders = list(itertools.permutations(range(n)))
    assert orders == [(0,)]
    chi = chromatic_number(n, edges)
    assert chi == 1
    records = []
    total = 0
    for order in orders:
        used, trace = greedy_coloring(n, edges, order)
        assert used == 1
        waste = used - chi
        assert waste == 0
        total += waste
        records.append({"order": list(order), "trace": trace,
                        "greedy_colors": used, "chromatic_number": chi, "waste": waste})
    expected = Fraction(total, len(orders))
    assert expected == 0
    # For a >= 0, a^2 < a implies a < sqrt(a), hence a - sqrt(a) < 0.
    # This verifies the radical inequality with rational arithmetic only.
    a = Fraction(n, 2)
    assert 0 <= a and a*a < a
    print(json.dumps({"status": "PASS", "n": n, "edges": [],
        "order_count": len(orders), "orders": records,
        "uniform_expected_waste": str(expected),
        "bound": "1/2 - sqrt(1/2)",
        "exact_negative_bound_certificate": {"a": str(a), "a_squared": str(a*a),
                                             "a_squared_less_than_a": a*a < a},
        "scope": "single exhibited graph; no inference from bounded enumeration"}, indent=2))


if __name__ == "__main__":
    main()
