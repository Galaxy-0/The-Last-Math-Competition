"""Exact supplementary residue-orbit checks; the infinite-period bridge is in Lean."""
import json
from math import isqrt

def orbit(modulus, expected):
    a,b=0,1
    first_returns=[]
    for index in range(1,expected+1):
        a,b=b,(a+b)%modulus
        if (a,b)==(0,1):
            first_returns.append(index)
    if first_returns != [expected]:
        raise RuntimeError((modulus,first_returns))
    return {'modulus':modulus,'least_positive_return':expected,
            'earlier_positive_returns':[], 'terminal_pair':[a,b]}

def main():
    p=7
    if p<2 or any(p%d==0 for d in range(2,isqrt(p)+1)):
        raise RuntimeError('Not prime')
    records=[orbit(p,16),orbit(p*p,112)]
    if any(p*p%r['least_positive_return']==0 for r in records):
        raise RuntimeError('Expected failure of divisibility')
    print(json.dumps({'p':p,'prime':True,'below_10_to_17':p<10**17,
                     'orbits':records,'periods_equal':16==112,
                     'scope':'Literal period-divisibility clause only, not a conventional Wall--Sun--Sun prime.'},indent=2))

if __name__=='__main__':main()
