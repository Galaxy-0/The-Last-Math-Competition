"""Supplemental exact checks; the complete formal proof is in lean/Main.lean."""
from fractions import Fraction as F
from itertools import combinations
import json
L=[[F(2 if i==j else -1) for j in range(3)] for i in range(3)]
Q=[[F(2 if i==j else -1,9) for j in range(3)] for i in range(3)]
def mul(A,B): return [[sum(A[i][k]*B[k][j] for k in range(3)) for j in range(3)] for i in range(3)]
def transpose(A): return [list(row) for row in zip(*A)]
assert mul(mul(L,Q),L)==L and mul(mul(Q,L),Q)==Q
assert transpose(mul(L,Q))==mul(L,Q) and transpose(mul(Q,L))==mul(Q,L)
R={(i,j):Q[i][i]+Q[j][j]-Q[i][j]-Q[j][i] for i in range(3) for j in range(3)}
assert all(v==(0 if i==j else F(2,3)) for (i,j),v in R.items())
edges=list(combinations(range(3),2))
trees=[]
for chosen in combinations(edges,2):
    seen={0}
    for _ in range(3):
        for a,b in chosen:
            if a in seen or b in seen: seen.update((a,b))
    if len(seen)==3: trees.append(chosen)
unordered=sum(R[i,j] for i,j in edges)
ordered=sum(R.values())
assert len(trees)==3 and unordered==2 and ordered==4
print(json.dumps({'trees':len(trees),'unordered_sum':str(unordered),'ordered_sum':str(ordered),'four_moore_penrose_equations':True}))
