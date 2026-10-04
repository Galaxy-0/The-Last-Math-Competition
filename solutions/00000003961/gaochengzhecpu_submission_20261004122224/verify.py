"""Exact finite cross-check of the Johnson k=1 witness; the Lean proof is general."""
from fractions import Fraction as F
from itertools import combinations
import json


def multiply(a, b):
    n = len(a)
    return [[sum((a[i][k] * b[k][j] for k in range(n)), F(0))
             for j in range(n)] for i in range(n)]


def check(n):
    vertices = [frozenset(s) for s in combinations(range(n), 1)]
    adj = [[len(s ^ t) == 2 for t in vertices] for s in vertices]
    degree = [sum(row) for row in adj]
    assert degree == [n - 1] * n
    p = [[F(1, 2) if i == j else F(1, 2 * degree[i]) if adj[i][j] else F(0)
          for j in range(n)] for i in range(n)]
    assert all(x > 0 for row in p for x in row)
    assert all(sum(row) == 1 for row in p)
    assert all(sum(p[i][j] for i in range(n)) == 1 for j in range(n))
    pi = [F(1, n)] * n
    assert [sum(pi[i] * p[i][j] for i in range(n)) for j in range(n)] == pi
    pt = [[F(i == j) for j in range(n)] for i in range(n)]
    a = F(n - 2, 2 * (n - 1))
    distances = []
    for t in range(6):
        expected = F(n - 1, n) * a ** t
        for i in range(n):
            assert sum(pt[i]) == 1 and all(x >= 0 for x in pt[i])
            for j in range(n):
                assert pt[i][j] == a ** t * F(i == j) + (1 - a ** t) / n
            actual_tv = sum(abs(pt[i][j] - pi[j]) for j in range(n)) / 2
            assert actual_tv == expected
        distances.append(expected)
        if t != 5:
            pt = multiply(pt, p)
    quarter = next(t for t, d in enumerate(distances) if d <= F(1, 4))
    three_quarters = next(t for t, d in enumerate(distances) if d <= F(3, 4))
    assert (quarter, three_quarters) == (2, 1)
    return {"N": n, "k": 1, "vertices": len(vertices), "degree": degree[0],
            "distance_at_times_0_to_5": [str(d) for d in distances],
            "mixing_time_quarter": quarter,
            "mixing_time_three_quarters": three_quarters,
            "mixing_time_ratio": str(F(quarter, three_quarters))}


if __name__ == "__main__":
    print(json.dumps({"method": "actual subset graphs and exact Fraction matrix powers",
                      "scope": "finite cross-check only; general theorem is proved in Lean",
                      "cases": [check(n) for n in (5, 6, 8, 12, 20)]}, indent=2))
