"""Exhaustive supporting checks for conjecture 7744, using exact arithmetic.

This is not a proof of the asymptotic assertion. It enumerates every labeled
simple cubic graph on 4 and 6 vertices and calculates the squared adjacency
matrix, normalized trace, uniform expectation and centered variance directly.
The submitted Lean project provides the general mathematical argument.
"""

from fractions import Fraction
from itertools import combinations
import json


def ensemble(n, degree):
    pairs = list(combinations(range(n), 2))
    if n * degree % 2:
        return []
    result = []
    for edges in combinations(pairs, n * degree // 2):
        degrees = [0] * n
        for u, v in edges:
            degrees[u] += 1
            degrees[v] += 1
        if degrees != [degree] * n:
            continue
        adjacency = [[0] * n for _ in range(n)]
        for u, v in edges:
            adjacency[u][v] = adjacency[v][u] = 1
        # Compute every entry of A squared, independently of the degree test.
        square = [
            [sum(adjacency[i][k] * adjacency[k][j] for k in range(n))
             for j in range(n)]
            for i in range(n)
        ]
        trace = sum(square[i][i] for i in range(n))
        assert all(square[i][i] == degree for i in range(n))
        assert trace == n * degree
        result.append(Fraction(trace, n))
    return result


def check(n, degree, expected_count):
    traces = ensemble(n, degree)
    assert len(traces) == expected_count and traces
    expectation = sum(traces, Fraction(0)) / len(traces)
    centered = [value - expectation for value in traces]
    assert all(value == 0 for value in centered)
    # Var(sqrt(n) * X) = n * E[X^2] when X is centered. No floating point.
    scaled_variance = n * sum((value * value for value in centered), Fraction(0)) / len(traces)
    proposed_variance = 4 - Fraction(12, degree) + Fraction(8, degree * degree)
    assert expectation == degree and scaled_variance == 0
    assert proposed_variance == Fraction(8, 9) and proposed_variance != scaled_variance
    return {
        "vertices": n,
        "degree": degree,
        "labeled_simple_regular_graph_count": len(traces),
        "normalized_quadratic_trace_values": sorted(map(str, set(traces))),
        "uniform_expectation": str(expectation),
        "centered_values": sorted(map(str, set(centered))),
        "sqrt_n_scaled_variance": str(scaled_variance),
        "conjectured_limiting_variance": str(proposed_variance),
        "result": "PASS",
    }


def main():
    # On 4 vertices the only cubic graph is K4. On 6 vertices its complement
    # is a simple 2-regular graph: one 6-cycle (5!/2 = 60 choices), or two
    # disjoint triangles (binomial(6,3)/2 = 10 choices). Thus 70 in total.
    result = {
        "scope": "Exhaustive finite supporting computation; not an asymptotic proof",
        "arithmetic": "Exact integers and fractions only",
        "cases": [check(4, 3, 1), check(6, 3, 70)],
        "result": "PASS",
    }
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
