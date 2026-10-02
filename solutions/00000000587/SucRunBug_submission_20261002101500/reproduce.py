# Independent finite checks; the full proof is in main.tex and lean4/.
from math import isqrt,sqrt
S={2*a+3*b for a in range(60) for b in range(60)}
ap={s for s in S if s-25 not in S}
assert ap=={0,*range(2,25),26}
squares={s for s in ap if isqrt(s)**2==s}
assert squares=={0,4,9,16} and len(squares-{0})>sqrt(6)
print('PASS: Apery(<2,3>,25) has positive squares 4,9,16, exceeding sqrt(6)')
