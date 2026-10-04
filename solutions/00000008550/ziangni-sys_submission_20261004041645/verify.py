"""Independent exhaustive finite check; the Lean proof is kernel checked separately."""
from itertools import product
C = range(3)

def congruent(r):
    rel = lambda x,y: r[3*x+y]
    return (all(rel(x,x) for x in C)
        and all(not rel(x,y) or rel(y,x) for x,y in product(C,repeat=2))
        and all(not (rel(x,y) and rel(y,z)) or rel(x,z) for x,y,z in product(C,repeat=3))
        and all(not (rel(x,xx) and rel(y,yy)) or
            (rel(min(x,y),min(xx,yy)) and rel(max(x,y),max(xx,yy)))
            for x,xx,y,yy in product(C,repeat=4)))

def ideal(K):
    return (0 in K and all(not (x<=y and y in K) or x in K for x,y in product(C,repeat=2))
        and all(not (x in K and y in K) or max(x,y) in K for x,y in product(C,repeat=2)))

quotients = [(0,1,2),(0,1,1),(0,0,1),(0,0,0)]
for q in quotients:
    target = range(max(q)+1)
    assert set(q)==set(target) and q[0]==0 and q[2]==max(q)
    assert all(q[min(x,y)]==min(q[x],q[y]) and q[max(x,y)]==max(q[x],q[y])
               for x,y in product(C,repeat=2))
relations = list(product((False,True),repeat=9))
congruences = [r for r in relations if congruent(r)]
kernels = {tuple(x for x in C if r[x]) for r in congruences}
ideals = {tuple(x for x,b in zip(C,bits) if b) for bits in product((False,True),repeat=3)
          if ideal({x for x,b in zip(C,bits) if b})}
quotient_relations = {tuple(q[x]==q[y] for x,y in product(C,repeat=2)) for q in quotients}
assert set(congruences)==quotient_relations and len(congruences)==4
assert kernels==ideals=={(0,),(0,1),(0,1,2)}
assert quotients[0]!=quotients[1]
assert tuple(x for x in C if quotients[0][x]==0)==tuple(x for x in C if quotients[1][x]==0)==(0,)
print('All 512 relations and all 8 subsets checked.')
print('4 genuine bounded-lattice surjections; their distinct kernel congruences exhaust all 4 congruences.')
print('3 ideals, all realized as quotient zero kernels:', sorted(kernels))
print('Identity and upper-threshold quotient have distinct congruences and equal zero kernel {0}.')
