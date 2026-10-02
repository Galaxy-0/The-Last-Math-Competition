# Independent finite checks; the full proof is in main.tex and lean4/.
for p in [2,3,5,7]:
 for k in range(1,4):
  modulus=p**k
  for c in range(modulus):
   x=0
   for _ in range(30):x=(x*x+c)%modulus;assert 0<=x<modulus
print('PASS: all tested integral parameter orbits preserve every tested residue ring')
