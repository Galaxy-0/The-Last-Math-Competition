"""Independent all-edge-mask enumeration; finite supporting check only."""

from collections import Counter
from fractions import Fraction
import json


def verify(n):
    possible_edges = [(i, j) for i in range(n) for j in range(i + 1, n)]
    graph_count = 0
    trace_counts = Counter()
    complement_components = Counter()
    for edge_mask in range(1 << len(possible_edges)):
        rows = [0] * n
        for bit, (i, j) in enumerate(possible_edges):
            if edge_mask & (1 << bit):
                rows[i] |= 1 << j
                rows[j] |= 1 << i
        if not all(row.bit_count() == 3 for row in rows):
            continue
        graph_count += 1
        # A symmetric adjacency matrix has the following diagonal of A*A.
        diagonal = [sum(((rows[i] >> k) & 1) * ((rows[k] >> i) & 1)
                        for k in range(n)) for i in range(n)]
        assert diagonal == [3] * n
        trace_counts[Fraction(sum(diagonal), n)] += 1
        if n == 6:
            complement_rows = [(((1 << n) - 1) ^ (1 << i)) ^ rows[i]
                               for i in range(n)]
            unseen = set(range(n))
            sizes = []
            while unseen:
                start = unseen.pop()
                reached = {start}
                frontier = [start]
                while frontier:
                    i = frontier.pop()
                    neighbors = {j for j in unseen
                                 if (complement_rows[i] >> j) & 1}
                    unseen.difference_update(neighbors)
                    reached.update(neighbors)
                    frontier.extend(neighbors)
                sizes.append(len(reached))
            complement_components[tuple(sorted(sizes))] += 1
    expectation = sum((value * count for value, count in trace_counts.items()),
                      Fraction(0)) / graph_count
    variance = n * sum(((value - expectation) ** 2 * count
                        for value, count in trace_counts.items()),
                       Fraction(0)) / graph_count
    assert graph_count == {4: 1, 6: 70}[n]
    assert expectation == 3 and variance == 0
    if n == 6:
        assert complement_components == Counter({(6,): 60, (3, 3): 10})
    return {
        "n": n,
        "edge_subsets_inspected": 1 << len(possible_edges),
        "cubic_graph_count": graph_count,
        "quadratic_trace_frequencies": {str(k): v for k, v in trace_counts.items()},
        "expectation": str(expectation),
        "sqrt_n_scaled_variance": str(variance),
        "complement_component_frequencies": {str(k): v for k, v in complement_components.items()},
    }


if __name__ == "__main__":
    print(json.dumps({"scope": "Finite supporting computation only",
                      "cases": [verify(4), verify(6)], "result": "PASS"}, indent=2))
