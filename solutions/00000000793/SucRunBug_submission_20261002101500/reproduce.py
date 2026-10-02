# Independent finite checks; the full proof is in main.tex and lean4/.
from math import isqrt
primes=[q for q in range(2,5000) if all(q%d for d in range(2,isqrt(q)+1))]
def digitsum(q):
 s=0
 while q:s+=q%3;q//=3
 return s
assert [q for q in primes if digitsum(q)%2==0]==[2]
for N in range(1,len(primes)+1):assert sum(digitsum(q)%2==0 for q in primes[:N])==1
print('PASS: only prime 2 has even base-three digit sum in the tested range')
