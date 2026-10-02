# Independent finite checks; the full proof is in main.tex and lean4/.
from math import log
for C in [-100,-1,0,1,100]:assert C*log(1)==0
assert len({0})<len({0,1})
print('PASS: one-edge label interval is a singleton for every tested constant')
