# Independent finite sanity checks; see the general proof and Lean project.
from math import isqrt

def prime(n):
    return n >= 2 and all(n % d for d in range(2, isqrt(n)+1))

from fractions import Fraction
from math import pi,sqrt
for p in range(3,150):
    if not prime(p):continue
    sq={x*x%p for x in range(p)}
    assert len(sq)==(p+1)//2
    for c in range(p):
        image={(x*x+c)%p for x in range(p)}
        assert 2*len(image)==p+1
        assert Fraction(len(image),p)==Fraction(1,2)+Fraction(1,2*p)
        assert Fraction(len(image),p)>Fraction(1,2)
assert 1-sqrt(pi/8)<.5
print('PASS: exact image formula for all p<150 and every c; claimed coefficient differs')
