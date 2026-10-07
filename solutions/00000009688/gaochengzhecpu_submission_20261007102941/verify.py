"""Supplementary exact polynomial arithmetic; infinite complex zeros are proved in Lean."""
import json

f = {0: -1, 1: 1}
g = {2: -1, 3: 1}
h = {2: 1, 3: 1}
shifted_f = {n + 2: c for n, c in f.items()}
assert shifted_f == g
assert set(f).isdisjoint(g) and set(f).isdisjoint(h)
assert set(g) == set(h)
assert sum(f.values()) == sum(g.values()) == 0
assert sum(h.values()) == 2
print(json.dumps({"status": "PASS", "coefficients": {"f": f, "g": g, "h": h},
                  "supports": [[0, 1], [2, 3], [2, 3]],
                  "identity": "g(X)=X^2*f(X)",
                  "values_at_X_1": [0, 0, 2],
                  "scope": "Exact supplementary algebra; universal and infinite assertions are Lean theorems."}, indent=2))
