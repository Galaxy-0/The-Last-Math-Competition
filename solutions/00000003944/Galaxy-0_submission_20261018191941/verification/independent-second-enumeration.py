from itertools import product,combinations
E={(0,1),(1,2),(0,2),(3,4),(4,5),(3,5),(0,3),(1,4),(2,5),(0,6),(0,7)}
V=range(8); adj={v:set() for v in V}
for u,v in E:adj[u].add(v);adj[v].add(u)
C=[c for c in product(range(3),repeat=8) if all(c[u]!=c[v] for u,v in E)]
S=set(C); graph={c:set() for c in C}
for c in C:
 for a,b in combinations(range(3),2):
  remaining={v for v in V if c[v] in {a,b}}
  while remaining:
   seed=min(remaining); comp={seed}; frontier=[seed]
   while frontier:
    x=frontier.pop()
    for y in adj[x]&remaining:
     if y not in comp:comp.add(y);frontier.append(y)
   remaining-=comp
   d=tuple((b if c[v]==a else a) if v in comp else c[v] for v in V)
   assert d in S
   assert (c[3]==c[1]) == (d[3]==d[1])
   graph[c].add(d)
left=set(C); classes=[]
while left:
 seed=min(left); seen={seed}; frontier=[seed]
 while frontier:
  x=frontier.pop()
  for y in graph[x]-seen:seen.add(y);frontier.append(y)
 left-=seen;classes.append(seen)
print('degrees', [len(adj[v]) for v in V])
print('proper colorings',len(C),'Kempe classes',sorted(map(len,classes)))
print('class invariant c(3)=c(1), sizes',sum(c[3]==c[1] for c in C),sum(c[3]!=c[1] for c in C))
print('directed transitions',sum(map(len,graph.values())))
assert sorted(map(len,classes))==[24,24]
