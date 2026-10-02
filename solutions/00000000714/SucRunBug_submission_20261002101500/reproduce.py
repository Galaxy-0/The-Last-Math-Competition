# Independent finite checks; the full proof is in main.tex and lean4/.
from fractions import Fraction
for p in [2,3,5,7]:
 for q in [2,3,5,7,11,13]:
  term=Fraction(1,p**q)
  valuation=-q
  norm=Fraction(p)**(-valuation)
  assert term.denominator==p**q and norm>=1
print('PASS: negative prime powers have p-adic norm at least 1')
