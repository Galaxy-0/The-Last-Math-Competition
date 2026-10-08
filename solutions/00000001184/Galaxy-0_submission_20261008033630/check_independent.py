#!/usr/bin/env python3
"""Independent finite arithmetic checks. Exact probability is supplemental, not needed by Lean."""
from itertools import product
from collections import Counter
from pathlib import Path
import ast, json
# Independent quotient construction: equivalence classes under simultaneous negation.
raw = [m for m in product(range(5),repeat=4) if (m[0]*m[3]-m[1]*m[2])%5==1]
neg = lambda m: tuple(-x%5 for x in m)
rep = lambda m: min(m,neg(m))
G=sorted(set(map(rep, raw))); index={x:i for i,x in enumerate(G)}
def rawmul(A,B):
 a,b,c,d=A;e,f,g,h=B
 return ((a*e+b*g)%5,(a*f+b*h)%5,(c*e+d*g)%5,(c*f+d*h)%5)
def mul(A,B):return rep(rawmul(A,B))
def inv(A):
 a,b,c,d=A
 return rep((d,-b%5,-c%5,a))
e=(1,0,0,1)
assert len(raw)==120 and len(G)==60
assert all(sum(rep(x)==g for x in raw)==2 for g in G)
assert all(mul(rep(x),rep(y))==rep(rawmul(x,y)) for x in raw for y in raw)
assert all(mul(x,y) in index for x in G for y in G)
assert all(mul(x,e)==x and mul(e,x)==x for x in G)
assert all(mul(x,inv(x))==e and mul(inv(x),x)==e for x in G)
assert all(mul(mul(x,y),z)==mul(x,mul(y,z)) for x in G for y in G for z in G)
def closure(a,b):
 found={e}; todo=[e]
 while todo:
  x=todo.pop()
  for s in (a,b):
   y=mul(x,s)
   if y not in found: found.add(y);todo.append(y)
 return found
sizes=Counter(len(closure(a,b)) for a in G for b in G)
# Parse worker Lean subgroup list, not its multiplication table.
text=(Path(__file__).resolve().parent / 'Counterexample.lean').read_text()
subtext=text.split('def subgroups : List (List Matrix) := ')[1].split('\n\ndef subgroupCheck')[0]
subs=list(map(set,ast.literal_eval(subtext)))
assert all(H < set(G) for H in subs)
assert all(e in H and all(inv(x) in H for x in H) and all(mul(x,y) in H for x in H for y in H) for H in subs)
covered={(x,y) for H in subs for x in H for y in H}
witness=(0,1,4,3)
assert witness in G and all(witness not in H for H in subs)
assert len(covered)==888 and 3600-len(covered)==2712
assert 25*(3600-len(covered)) < 19*3600
print(json.dumps({'raw_order':len(raw),'quotient_order':len(G),'pair_generated_subgroup_sizes':dict(sorted(sizes.items())),'certified_subgroup_sizes':[len(H) for H in subs],'certified_nongenerating_pairs':len(covered),'upper_bound_numerator':3600-len(covered),'required_numerator':2736,'identity':e,'common_missing_witness':witness},indent=2))
