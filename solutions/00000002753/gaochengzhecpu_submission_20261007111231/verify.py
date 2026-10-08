"""Supplemental exact free-word and matrix checks."""
import json
words={'XYZ':1,'YXZ':-1,'ZXY':-1,'ZYX':1}
assert len(words)==4 and all(words.values())
A=[[0,1],[0,0]]
B=[[0,0],[1,0]]
def mul(U,V):return [[sum(U[i][k]*V[k][j] for k in range(2)) for j in range(2)] for i in range(2)]
def sub(U,V):return [[U[i][j]-V[i][j] for j in range(2)] for i in range(2)]
def comm(U,V):return sub(mul(U,V),mul(V,U))
out=comm(comm(A,B),A)
assert out==[[0,2],[0,0]]
print(json.dumps({'free_words':words,'nonzero_evaluation':out}))
