"""Exact rational examples only; the all-dimension theorems are in Lean."""
from fractions import Fraction as Q
import json

reports=[]
for n in range(2,13):
    u=[[Q(int(i==j)) for j in range(n)] for i in range(n)]
    overlaps=[]
    for i in range(n):
        assert sum(a*a for a in u[i])==1
        assert [Q(j)*u[i][j] for j in range(n)]==[Q(i)*x for x in u[i]]
        for j in range(i+1,n):
            overlaps.append(sum(a*b for a,b in zip(u[i],u[j]))**2)
    assert len(overlaps)==n*(n-1)//2
    mean=sum(overlaps)/len(overlaps)
    assert all(x==0 for x in overlaps) and mean==0 and Q(n)*mean!=2
    reports.append({'n':n,'pairs':len(overlaps),'exact_mean':str(mean),
                    'claimed_mean':str(Q(2,n))})
# A non-diagonal symmetric matrix with rational normalized eigenvectors.
A=[[Q(61,25),Q(48,25)],[Q(48,25),Q(89,25)]]
vectors=[[Q(4,5),Q(-3,5)],[Q(3,5),Q(4,5)]]
for v,e in zip(vectors,[Q(1),Q(5)]):
    # Eigenvalues are checked from A rather than supplied by numerical diagonalization.
    actual=[sum(a*b for a,b in zip(row,v)) for row in A]
    assert actual==[e*x for x in v]
assert sum(a*b for a,b in zip(*vectors))==0
print(json.dumps({'status':'PASS','diagonal_examples':reports,
                  'non_diagonal_exact_example':'PASS',
                  'scope':'Finite supplemental checks; full proof in Lean.'},indent=2))
