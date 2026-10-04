"""Independent exact rank-one Hecke/KL check, using only Python stdlib."""
from collections import defaultdict

# Laurent polynomials represented sparsely by {exponent of v: integer}.
def add(a, b):
    c = defaultdict(int, a)
    for k, x in b.items():
        c[k] += x
    return {k: x for k, x in c.items() if x}

def shift(a, n):
    return {k+n: x for k, x in a.items()}

def bar_scalar(a):
    return {-k: x for k, x in a.items()}

# Hecke element (coefficient of identity, coefficient of T_s).
# bar(T_s) = v^-2 T_s + v^-2 - 1.
def bar(a):
    c, t = map(bar_scalar, a)
    return add(c, add(shift(t, -2), {k: -x for k, x in t.items()})), shift(t, -2)

canonical_s = ({-1: 1}, {-1: 1})
assert bar(canonical_s) == canonical_s
# Lower coefficient is strictly negative and leading coefficient is v^-1.
assert all(k < 0 for k in canonical_s[0])
assert canonical_s[1] == {-1: 1}
# Multiplication by v reads the P_{x,s}(v^2) coefficients.
assert [shift(a, 1) for a in canonical_s] == [{0: 1}, {0: 1}]

table = {('e', 'e'): {0: 1}, ('e', 's'): {0: 1},
         ('s', 'e'): {}, ('s', 's'): {0: 1}}
length = {'e': 0, 's': 1}
for (x, w), p in table.items():
    comparable = (x, w) != ('s', 'e')
    if not comparable:
        assert not p  # zero has no leading nonzero coefficient
        continue
    assert p.get(0) == 1
    if x == w:
        assert p == {0: 1}
    else:
        assert 2 * max(p) < length[w] - length[x]
    assert p[max(p)] == 1
print('PASS: exact rank-one Hecke bar invariance and KL normalization')
print('PASS: all four pairs; nonzero leading coefficients = 1; zero excluded')
