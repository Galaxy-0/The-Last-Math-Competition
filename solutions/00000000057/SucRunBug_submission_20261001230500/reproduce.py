# Independent finite sanity checks; see the general proof and Lean project.
from math import isqrt

def prime(n):
    return n >= 2 and all(n % d for d in range(2, isqrt(n)+1))

from itertools import permutations
for m in [1,2,10,100]:
    vertices=[(i,j) for i in range(m) for j in range(4)]
    adj=lambda u,v: u[0]==v[0] and u[1]!=v[1]
    assert len(vertices)==4*m
    assert all(sum(adj(u,v) for v in vertices)==3 for u in vertices)
# Any cycle stays inside one component. Independently enumerate its simple cycles.
lengths=set()
for k in range(3,5):
    for cyc in permutations(range(4),k):
        if all(cyc[i]!=cyc[(i+1)%k] for i in range(k)):lengths.add(k)
assert lengths=={3,4}
assert {k for k in lengths if prime(k)}=={3}
print('PASS: finite instances have degree 3; one component has prime cycle lengths {3}')
