"""Independent exact verification using the GF(2) subset-nullity definition.

No numerical root finding, external algebra package, or Lean output is used.
This is supplementary evidence; the Lean file contains the formal proof.
"""
from collections import Counter
from fractions import Fraction
from math import comb
import json


def gf2_rank(rows, columns):
    rows = rows[:]
    rank = 0
    for column in range(columns):
        pivot = next((j for j in range(rank, len(rows))
                      if rows[j] & (1 << column)), None)
        if pivot is None:
            continue
        rows[rank], rows[pivot] = rows[pivot], rows[rank]
        for j in range(len(rows)):
            if j != rank and rows[j] & (1 << column):
                rows[j] ^= rows[rank]
        rank += 1
    return rank


def subset_nullities(adjacency):
    """Histogram of dim ker A[S], for every S including the empty subset."""
    n = len(adjacency)
    histogram = Counter()
    for mask in range(1 << n):
        vertices = [i for i in range(n) if mask & (1 << i)]
        rows = [sum(adjacency[i][j] << k for k, j in enumerate(vertices))
                for i in vertices]
        histogram[len(vertices) - gf2_rank(rows, len(vertices))] += 1
    assert sum(histogram.values()) == 1 << n
    return dict(sorted(histogram.items()))


def coefficients(histogram):
    """Expand sum histogram[k]*(x-1)^k, returning ascending coefficients."""
    out = [0] * (1 + max(histogram))
    for k, count in histogram.items():
        for j in range(k + 1):
            out[j] += count * comb(k, j) * (-1) ** (k - j)
    return out


def multiply(a, b):
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] += x * y
    return out


def evaluate(coeffs, x):
    return sum(c * x ** i for i, c in enumerate(coeffs))


def main():
    graphs = {}
    for n in (5, 10):
        A = [[int(i // 5 == j // 5 and abs(i - j) == 1)
              for j in range(n)] for i in range(n)]
        assert all(A[i][i] == 0 for i in range(n))
        assert all(A[i][j] == A[j][i] for i in range(n) for j in range(n))
        histogram = subset_nullities(A)
        coeffs = coefficients(histogram)
        graphs[n] = {
            "vertices": n,
            "edges": [[i, j] for i in range(n) for j in range(i + 1, n) if A[i][j]],
            "all_subsets_checked": 1 << n,
            "nullity_histogram": histogram,
            "ascending_integer_coefficients": coeffs,
            "value_at_2": evaluate(coeffs, 2),
        }
    assert graphs[5]["ascending_integer_coefficients"] == [0, 2, 5, 1]
    assert graphs[10]["ascending_integer_coefficients"] == [0, 0, 4, 20, 29, 10, 1]
    assert graphs[10]["ascending_integer_coefficients"] == multiply(
        graphs[5]["ascending_integer_coefficients"], graphs[5]["ascending_integer_coefficients"])
    assert graphs[10]["value_at_2"] == 1024
    # Exact bracketing of the negative quadratic root: (-5,-4).
    h = [2, 5, 1]
    assert evaluate(h, Fraction(-5)) == 2
    assert evaluate(h, Fraction(-4)) == -2
    assert 17 > 3 ** 2
    print(json.dumps({"status": "PASS", "method": "GF(2) subset-nullity enumeration",
                      "graphs": graphs, "real_root": "(-5 - sqrt(17))/2 < -4"},
                     indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
