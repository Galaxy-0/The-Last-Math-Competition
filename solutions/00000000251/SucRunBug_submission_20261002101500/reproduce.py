# Independent finite checks; the full proof is in main.tex and lean4/.
from itertools import product
for labels in product(range(1),repeat=2):assert len(set(labels))<2
print('PASS: no injective map from two vertices to the one residue modulo 1')
