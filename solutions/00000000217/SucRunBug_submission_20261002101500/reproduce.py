# Independent finite checks; the full proof is in main.tex and lean4/.
from math import exp
assert exp(-exp(1))<1<exp(1/exp(1))
x=1
for _ in range(100):x=1**x;assert x==1
print('PASS: base-one finite towers stay at algebraic value 1; base is strictly interior')
