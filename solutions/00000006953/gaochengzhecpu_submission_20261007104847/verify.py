"""Exact enumeration of the complete independent binary sample space; no simulation."""
from fractions import Fraction as F
from itertools import product
import json

outcomes=list(product([-1,1],repeat=5))
assert len(outcomes)==32
def expectation(values): return sum(values,F(0))/len(values)
def variance(values):
    mean=expectation(values)
    return expectation([(x-mean)**2 for x in values])
first=[F(w[0]) for w in outcomes]
second=[F(2*w[0]) for w in outcomes]
assert expectation(first)==expectation(second)==0
assert variance(first)==1 and variance(second)==4
def estimator(n,w): return (F(sum(w[:n]),n)+F(2*sum(w[n:]),5-n))/2
rows=[]
for n in range(1,5):
    values=[estimator(n,w) for w in outcomes]
    assert expectation(values)==0
    var=variance(values)
    assert var==(F(1,n)+F(4,5-n))/4
    rows.append({'allocation':[n,5-n],'mean':str(expectation(values)),'variance':str(var)})
assert F(rows[0]['variance'])==F(1,2)
assert F(rows[1]['variance'])==F(11,24)<F(1,2)
assert F(1,4)==variance(first)/variance(second)
print(json.dumps({'status':'PASS','outcome_count':32,'each_outcome_probability':'1/32',
 'stratum_variances':['1','4'],'allocations':rows,
 'scope':'Exact complete enumeration; Mathlib probability integrals and variances independently proved in Lean.'},indent=2))
