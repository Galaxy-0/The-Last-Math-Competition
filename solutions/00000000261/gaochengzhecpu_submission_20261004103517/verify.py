"""Supplementary exact checks; the complete minimality proof is in Lean."""
import json
from math import isqrt

def value_le(d,t,u,s,v):
    if u<=v:
        return t<=s or (t-s)**2<=d*(v-u)**2
    return t<=s and d*(u-v)**2<=(s-t)**2

def main():
    d=5
    if d%4!=1 or any(d%(a*a)==0 for a in range(2,isqrt(d)+1)):
        raise RuntimeError('Discriminant check failed')
    if 1*1-d*1*1!=-4 or 3*3-d*1*1!=4:
        raise RuntimeError('Witness equations failed')
    samples=[]
    # This range is a supplemental sanity check, never the minimality proof.
    for u in range(1,501):
        for sign in [-4,4]:
            square=d*u*u+sign
            t=isqrt(square)
            if t*t==square and t%2==u%2:
                if not value_le(d,1,1,t,u):raise RuntimeError('Unit minimum check failed')
                if sign==4 and not value_le(d,3,1,t,u):raise RuntimeError('Positive minimum check failed')
                samples.append({'t':t,'u':u,'norm_numerator':sign})
    print(json.dumps({'d':d,'fundamental_discriminant':True,
        'witnesses':[{'t':1,'u':1,'u_divides_t':True},{'t':3,'u':1,'u_divides_t':True}],
        'supplementary_search_u_max':500,'sample_solutions':samples,
        'scope':'The finite list is only a cross-check. Unbounded minimality and uniqueness are proved in Lean.'},indent=2))
if __name__=='__main__':main()
