#!/usr/bin/env python3
"""Exact independent checks for the n=3 counterexample; standard library only."""

from collections import Counter
from itertools import permutations
import json
from math import factorial


def convolve(left, right):
    result = [0] * (len(left) + len(right) - 1)
    for i, a in enumerate(left):
        for j, b in enumerate(right):
            result[i + j] += a * b
    return result


def main():
    coefficients = [1]
    for i in range(1, 4):
        coefficients = convolve(coefficients, [1] * i)

    histogram = Counter(
        sum(p[i] > p[j] for i in range(3) for j in range(i + 1, 3))
        for p in permutations(range(3))
    )
    independent = [histogram[i] for i in range(4)]
    assert coefficients == [1, 2, 2, 1]
    assert independent == coefficients
    assert sum(coefficients) == factorial(3)
    assert coefficients[1] == coefficients[2] == max(coefficients)
    assert all(
        coefficients[i] ** 2 >= coefficients[i - 1] * coefficients[i + 1]
        for i in range(1, len(coefficients) - 1)
    )
    print(json.dumps({
        "n": 3,
        "coefficients": coefficients,
        "inversion_histogram": independent,
        "permutations_checked": sum(histogram.values()),
        "maximum": max(coefficients),
        "maximizing_degrees": [i for i, c in enumerate(coefficients)
                               if c == max(coefficients)],
        "log_concave": True,
        "flat_free": False,
    }, indent=2))


if __name__ == "__main__":
    main()
