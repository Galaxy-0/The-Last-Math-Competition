# Independent finite checks; the full proof is in main.tex and lean4/.
from itertools import product, permutations
latin=[]
for table in product(range(2),repeat=4):
 if all(len({table[2*i+j] for j in range(2)})==2 for i in range(2)) and all(len({table[2*i+j] for i in range(2)})==2 for j in range(2)):
  trans=[sigma for sigma in permutations(range(2)) if len({table[2*i+sigma[i]] for i in range(2)})==2]
  latin.append((table,len(trans)))
assert len(latin)==2 and all(count==0 for _,count in latin)
assert min(count for _,count in latin)==0
print('PASS: every order-two Latin square has zero transversals')
