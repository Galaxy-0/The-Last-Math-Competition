"""Independent exhaustive verification of actual C3 lattice congruences."""
from itertools import product
V=range(3)
def relation(mask):return tuple(bool(mask & (1<<(3*x+y))) for x in V for y in V)
def at(r,x,y):return r[3*x+y]
def congruent(r):
 return (all(at(r,x,x) for x in V)
  and all(not at(r,x,y) or at(r,y,x) for x,y in product(V,repeat=2))
  and all(not(at(r,x,y) and at(r,y,z)) or at(r,x,z) for x,y,z in product(V,repeat=3))
  and all(not(at(r,x,u) and at(r,y,v)) or at(r,min(x,y),min(u,v)) for x,u,y,v in product(V,repeat=4))
  and all(not(at(r,x,u) and at(r,y,v)) or at(r,max(x,y),max(u,v)) for x,u,y,v in product(V,repeat=4)))
def below(r,s):return all(not a or b for a,b in zip(r,s))
bottom=tuple(x==y for x in V for y in V)
alpha=tuple((x<=1 and y<=1) or x==y for x in V for y in V)
beta=tuple((x>=1 and y>=1) or x==y for x in V for y in V)
top=(True,)*9
congruences=[relation(mask) for mask in range(512) if congruent(relation(mask))]
assert set(congruences)=={bottom,alpha,beta,top}
atoms=[r for r in congruences if r!=bottom and all(s==bottom or s==r for s in congruences if below(s,r))]
assert set(atoms)=={alpha,beta} and len(atoms)==2
assert 3<2**len(atoms) # Equivalent to log_2(3)<atom_count because log base2 is increasing.
print('PASS: all 512 relation tables tested for equivalence AND min/max compatibility; exactly 4 congruences; exactly 2 distinct atoms; 3<4 proves the real logarithmic violation.')
