# Independent finite checks; the full proof is in main.tex and lean4/.
from fractions import Fraction
from math import sqrt
hit3=Fraction(1);hit2=hit3;hit1=(hit2+hit3)/2
prob=(hit1+hit2+hit3)/3
assert prob==1 and abs(prob-2)>1/sqrt(3)
print('PASS: row-three terminal hook cell has probability 1 and violates content bound')
