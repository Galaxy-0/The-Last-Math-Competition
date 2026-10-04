"""Exact sample checks; actual Galois-group order bounds are established by Lean."""
import json
from math import factorial


def check(d):
    assert d >= 2 and d % 2 == 0
    f = [-2, -1] + [0] * (d-2) + [1]
    q = [-2] + [(-1)**(k+1) for k in range(1, d)]
    product = [0] * (d+1)
    for k, a in enumerate(q):
        product[k] += a
        product[k+1] += a
    root_value = sum(a * (-1)**k for k, a in enumerate(f))
    assert root_value == 0
    assert product == f
    assert len(q)-1 == d-1 and q[-1] == 1
    assert factorial(d-1) < factorial(d)
    return {"degree": d, "value_at_minus_one": root_value,
            "quotient_degree": len(q)-1, "factorization": "PASS",
            "factorial_upper_bound": factorial(d-1),
            "symmetric_group_order": factorial(d), "passed": True}


if __name__ == "__main__":
    print(json.dumps({"checks": [check(d) for d in [2, 4, 6, 8, 10, 20]],
          "scope": "Exact root, factorization, degree, and factorial checks only; not a computation of exact Galois groups. The generic group-theoretic proof is in Lean."}, indent=2))
