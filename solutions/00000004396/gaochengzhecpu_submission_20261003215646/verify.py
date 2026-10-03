"""Independent finite-model check for conjecture 4396 only."""
from itertools import product
import json
from pathlib import Path

vertices=range(8)
edges={(i,j) for i in vertices for j in vertices if i<j and
       ((i+1)%8==j or (j+1)%8==i or (i+4)%8==j)}
assert len(edges)==12
maps=list(product(range(2),repeat=8))
assert len(maps)==len(set(maps))==256
hom=[f for f in maps if all(f[i]!=f[j] for i,j in edges)]
assert not hom
cycle=[0,1,2,3,4,0]
assert all(tuple(sorted((a,b))) in edges for a,b in zip(cycle,cycle[1:]))
left=(2*1)**len(edges)*2**8
right=len(hom)*2**(2*len(edges))
assert left>right
result={'conjecture':4396,'vertices':8,'edges':sorted(edges),
        'all_vertex_maps':len(maps),'hom_to_K2':len(hom),
        'density_inequality_cross_multiplied':[left,right],
        'pdf_checked':False}
Path(__file__).with_name('auxiliary-verification.json').write_text(
    json.dumps(result,indent=2)+'\n',encoding='utf-8')
print(json.dumps(result))
