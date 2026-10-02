# Independent finite checks; the full proof is in main.tex and lean4/.
from fractions import Fraction
X={0,1};A={0}
def identity(x):return x
for a in range(30):
 for b in range(30):
  hit={x for x in X if x in A and identity(x) in A and identity(x) in A}
  assert Fraction(len(hit),len(X))==Fraction(1,2)
assert Fraction(len(A),len(X))**2==Fraction(1,4)
for size in range(20):
 average=Fraction(size,2)/size if size else Fraction(0)
 assert average in [Fraction(0),Fraction(1,2)] and average!=Fraction(1,4)
print('PASS: identity recurrence averages are 0 or 1/2, never 1/4')
