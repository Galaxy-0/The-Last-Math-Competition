# Independent finite sanity checks; see the general proof and Lean project.
from math import isqrt

def prime(n):
    return n >= 2 and all(n % d for d in range(2, isqrt(n)+1))

for p in range(5,200):
    if not prime(p):continue
    d=p
    assert d not in [1,p-2]
    assert all(pow(x,d,p)==x for x in range(p))
    assert len({pow(x,d,p) for x in range(p)})==p
    assert len({(pow(x,d,p)+x)%p for x in range(p)})==p
print('PASS: d=p witnesses both permutations for every prime 3<p<200; unrestricted exponents only')
