"""Independent exact verification of the star witness and full spectral basis."""
from fractions import Fraction
from itertools import permutations
N=10
A=[[int((i==0)!=(j==0)) for j in range(N)] for i in range(N)]
L=[[sum(A[i])*(i==j)-A[i][j] for j in range(N)] for i in range(N)]
x=[0]+[1]*8+[-8]
def mv(v):return [sum(a*b for a,b in zip(row,v)) for row in L]
assert mv(x)==x
basis=[([1]*N,0)]
for i in range(1,9):
 v=[0]*N;v[i]=1;v[9]=-1;basis.append((v,1))
basis.append(([-9]+[1]*9,10))
for v,t in basis:assert mv(v)==[t*a for a in v]
M=[[Fraction(v[i]) for v,t in basis] for i in range(N)]
rank=0
for col in range(N):
 pivot=next((i for i in range(rank,N) if M[i][col]),None)
 if pivot is None:continue
 M[rank],M[pivot]=M[pivot],M[rank]
 q=M[rank][col];M[rank]=[a/q for a in M[rank]]
 for i in range(N):
  if i!=rank:
   q=M[i][col];M[i]=[a-q*b for a,b in zip(M[i],M[rank])]
 rank+=1
assert rank==N
for k in (3,4):
 assert not any(all(A[v[i]][v[(i+1)%k]] for i in range(k)) for v in permutations(range(N),k))
remaining=set(i for i in range(N) if x[i]);components=[]
while remaining:
 todo=[remaining.pop()];component=[]
 while todo:
  i=todo.pop();component.append(i)
  new=[j for j in remaining if A[i][j] and x[i]*x[j]>0]
  for j in new:remaining.remove(j);todo.append(j)
 components.append(component)
assert sorted(components)==[[i] for i in range(1,10)]
assert len(components)**2>4*N
print('PASS: exact D-A eigenvector, complete independent eigenbasis with spectrum0,1(x8),10; no3/4 cycles; nine singleton strong nodal domains;81>40.')
