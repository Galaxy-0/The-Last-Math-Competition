"""Finite regression tests of the documented model (not a Lean check)."""
from itertools import combinations_with_replacement, product

def cut_connected(n, edges, u, v):
    for mask in range(1 << n):
        inside = lambda w: (mask >> w) & 1
        if inside(u) and not inside(v) and all(inside(a) == inside(b) for a,b in edges):
            return False
    return True

def cut_rank(n, edges):
    return n - sum(all(not cut_connected(n,edges,u,v) or u <= v for v in range(n)) for u in range(n))

def uf_rank(n,edges):
    rep=list(range(n)); r=0
    for a,b in edges:
        x,y=rep[a],rep[b]
        if x!=y:
            rep=[x if c==y else c for c in rep];r+=1
    return r

def check(n,edges,q):
    full=cut_rank(n,edges)
    assert full==uf_rank(n,edges)
    result=0;objects=[]
    for mask in range(1<<len(edges)):
        subset=[e for i,e in enumerate(edges) if (mask>>i)&1]
        r=cut_rank(n,subset)
        assert r==uf_rank(n,subset) and r<=full and r<=len(subset)
        a,b=q**(full-r),(q-2)**(len(subset)-r)
        result+=a*b
        if len(edges)<=3:
            objects.extend((mask,i,j) for i in range(a) for j in range(b))
    assert result>=q**full>0
    if len(edges)<=3:
        assert len(objects)==len(set(objects))==result
    return result

def main():
    tests=0
    for n in range(4):
        possible=[(a,b) for a in range(n) for b in range(a,n)]
        for size in range(5):
            for es in combinations_with_replacement(possible,size):
                for q in (2,3,4):check(n,es,q);tests+=1
    assert check(1,[(0,0)],2)==1
    assert check(1,[(0,0)],3)==2
    assert check(2,[(0,1)],2)==3
    assert check(2,[(0,1),(0,1)],2)==4
    assert check(3,[(0,1),(1,2),(2,0)],2)==13
    print(f'PASS: {tests} graph/parameter cases; loops, parallel edges, empty graphs; cut rank agrees with union-find; rank bounds, positive bound, unique counts checked.')
if __name__=='__main__':main()
