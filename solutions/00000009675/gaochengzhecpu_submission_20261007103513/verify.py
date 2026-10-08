"""Exact supplemental arithmetic; the field-theoretic obstruction is proved in Lean."""
from math import gcd
import json

n=105
primes=[p for p in range(2,n+1) if n%p==0 and all(p%d for d in range(2,p))]
totatives=[k for k in range(1,n+1) if gcd(k,n)==1]
assert primes==[3,5,7]
assert len(totatives)==48 and len(totatives)//2==24
assert gcd(1,n)==gcd(2,n)==1
assert 24>2
print(json.dumps({'status':'PASS','N':n,'distinct_prime_divisors':primes,
 'totatives':totatives,'totient':len(totatives),'conjectured_degree':24,
 'reduced_denominators':[n,n],
 'scope':'Exact integer checks only; actual field transcendence-degree bound is proved in Lean.'},indent=2))
