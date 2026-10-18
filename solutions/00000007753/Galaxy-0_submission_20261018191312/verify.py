#!/usr/bin/env python3
"""Independent exact-arithmetic sanity check; Lean is the proof certificate."""
from fractions import Fraction as Q

def multiply(a, b):
    result = [Q(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            result[i+j] += x*y
    return result

for c, a, b in [(-2, [-2,1], [1,1]), (-6, [-3,1], [2,1])]:
    result = multiply(list(map(Q,a)), list(map(Q,b)))
    assert result == [Q(c),Q(-1),Q(1)]
    assert len(a) == len(b) == 2 and a[-1] == b[-1] == 1
    print(f'c={c}: {a} * {b} = {result}')
assert -2 != -6
assert 2 > 2**(1-1)
print('Two distinct reducible parameters exceed the asserted bound 1.')
