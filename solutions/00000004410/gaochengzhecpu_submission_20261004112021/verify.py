"""Supplemental finite probability checks; equality of all real limits is in Lean."""
import itertools, json, math
from fractions import Fraction as Q

def entropy(masses):
    assert all(x>=0 for x in masses) and sum(masses)==1
    return -sum(float(x)*math.log(float(x)) for x in masses if x)

checks=[]
for n in range(1,6):
    edges=list(itertools.combinations(range(n),2))
    outcomes=list(itertools.product((False,True),repeat=len(edges)))
    assert len(outcomes)==2**(n*(n-1)//2)
    uniform=[Q(1,len(outcomes))]*len(outcomes)
    copied=list(uniform)
    assert uniform==copied and entropy(uniform)==entropy(copied)
    empty=[Q(1)]+[Q(0)]*(len(outcomes)-1)
    assert entropy(empty)==0
    checks.append({'vertices':n,'outcomes':len(outcomes),
                   'uniform_entropy_per_vertex':entropy(uniform)/n,'empty_entropy':entropy(empty)})
print(json.dumps({'status':'PASS','finite_checks':checks,
                  'scope':'Finite checks only; all-window and real-limit proofs are in Lean.'},indent=2))
