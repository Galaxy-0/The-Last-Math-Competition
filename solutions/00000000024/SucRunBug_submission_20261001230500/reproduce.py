# Independent finite sanity checks; see the general proof and Lean project.
from math import isqrt

def prime(n):
    return n >= 2 and all(n % d for d in range(2, isqrt(n)+1))

from math import floor
from fractions import Fraction
from itertools import combinations
ps=[p for p in range(2,10000) if prime(p)]
xs=[Fraction(-1007,8),Fraction(-1,2),Fraction(0),Fraction(1,3),Fraction(123,7)]
for x in xs:
    for p in ps:
        assert floor(x+p)==floor(x)+p
        assert floor(x+p)%4 != floor(x)%4
        assert floor(x-p)%4 != floor(x)%4
vs=[0,2,5,7]
assert all(prime(abs(x-y)) for x,y in combinations(vs,2))
print('PASS: floor translation, prime residues, negative/nonintegral points, and four-clique')
