"""Exact illustrative checks of the actual finite sets; the infinite proof is Lean."""
import json


def check(n):
    powers = {2**i for i in range(2*n)}
    shifted = {1 + 2**i for i in range(2*n)}
    A = powers | shifted
    sums = {a + b for a in A for b in A}
    products = {a * b for a in A for b in A}
    intersection = sums & products
    values = {(i, j): 2**i + 2**(n+j) for i in range(n) for j in range(n)}
    assert all(isinstance(a, int) and a > 0 for a in A)
    assert 2*n <= len(A) <= 4*n
    assert len(set(values.values())) == n*n
    assert set(values.values()) <= intersection
    for (i, j), value in values.items():
        assert 2**i in A and 2**(n+j) in A
        assert 1 <= n+j-i < 2*n
        assert 1 + 2**(n+j-i) in A
        assert value == 2**i * (1 + 2**(n+j-i))
    assert len(intersection) >= n*n
    return {"n": n, "set_size": len(A), "intersection_size": len(intersection),
            "embedded_grid_size": len(values), "passed": True}


if __name__ == "__main__":
    rows = [check(n) for n in [1, 2, 3, 5, 10, 25]]
    print(json.dumps({"checks": rows,
          "scope": "Finite exact cross-checks only; arbitrary-size and asymptotic conclusions are proved in Lean."}, indent=2))
