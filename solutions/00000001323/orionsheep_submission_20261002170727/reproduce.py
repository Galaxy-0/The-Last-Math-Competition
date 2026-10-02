#!/usr/bin/env python3
"""Independent verification for the disproof of conjecture 00000001323."""
import sys, cmath

def qmul(a, b):
    c = [0]*7
    for i in range(4):
        for j in range(4):
            c[i+j] += a[i]*b[j]
    # reduce t^4 = -(t^3+t^2+t+1), t^5 = 1, t^6 = t
    r4, r5, r6 = c[4], c[5], c[6]
    out = [
        c[0] - r4 + r5,
        c[1] - r4 + r6,
        c[2] - r4,
        c[3] - r4,
    ]
    return out

def main():
    one = [1,0,0,0]; T = [0,1,0,0]; T2 = [0,0,1,0]; T3 = [0,0,0,1]
    T4 = [-1,-1,-1,-1]
    assert qmul(T, T4) == one and qmul(T4, T) == one
    assert qmul(T, T) == T2 and qmul(T2, T) == T3 and qmul(T3, T) == T4
    for k, P in [(1,T),(2,T2),(3,T3),(4,T4)]:
        assert P != one, f"t^{k} = 1"
    p = T4
    for k in range(2, 5):
        p = qmul(p, T4)
        assert p != one, f"(t^4)^{k} = 1"
    print("Z[zeta_5]: t has order exactly 5; t*t^4 = 1 (det diag = 1)")
    # numeric check with complex numbers
    z = cmath.exp(2j*cmath.pi/5)
    assert abs(z*z*z*z*z - 1) < 1e-12 and all(abs(z**k - 1) > 1e-6 for k in (1,2,3,4))
    import numpy as np
    A = np.array([[z, 0],[0, z**(-1)]])
    assert abs(np.linalg.det(A) - 1) < 1e-10
    I = np.eye(2)
    assert all(np.max(np.abs(np.linalg.matrix_power(A, k) - I)) > 1e-6 for k in (1,2,3,4))
    assert np.max(np.abs(np.linalg.matrix_power(A, 5) - I)) < 1e-10
    print("complex check: det(diag(z5,z5^-1)) = 1, A^k != I for k<5, A^5 = I")
    print("period 5 not in {1,2,3,4,6} -> conjecture refuted")
    return 0

if __name__ == "__main__":
    sys.exit(main())
