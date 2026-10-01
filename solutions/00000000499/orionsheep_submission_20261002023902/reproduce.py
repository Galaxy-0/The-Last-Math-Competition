#!/usr/bin/env python3
"""Independent recomputation for the disproof of TLMC conjecture 00000000499.

Two nonintersecting simple random walks on Z with ordered starts
(x1, x2) = (0, 4) and endpoints (y1, y2) = (1, 3).  Each walk moves +-1 per step;
all 4^T joint step sequences are equally likely (probability 1/4^T each).
We count joint paths that reach the prescribed endpoints and satisfy the strict
order w1(t) < w2(t) at every time t = 0..T.  Exact rational arithmetic, stdlib only.

Expected output:
    P(T=1) = 1/4,  P(T=2) = 0,  P(T=3) = 1/8  (and p(4)=0, p(5)=75/1024).
Since the conjecture's right-hand side (GUE ordered-eigenvalue density at the
endpoints times the Vandermonde factor) contains no T, it is a single constant and
cannot equal both 1/4 and 1/8; the conjecture is FALSE.
"""
from fractions import Fraction
from itertools import product

START = (0, 4)
END = (1, 3)


def p_hit(T: int) -> Fraction:
    total = 4 ** T
    good = 0
    for s1 in product((1, -1), repeat=T):
        w1 = [START[0]]
        for d in s1:
            w1.append(w1[-1] + d)
        if w1[-1] != END[0]:
            continue
        for s2 in product((1, -1), repeat=T):
            w2 = [START[1]]
            for d in s2:
                w2.append(w2[-1] + d)
            if w2[-1] != END[1]:
                continue
            if all(a < b for a, b in zip(w1, w2)):
                good += 1
    return Fraction(good, total)


def main() -> None:
    vals = {T: p_hit(T) for T in range(1, 6)}
    for T, p in vals.items():
        print(f"P(T={T}) = {p} = {float(p):.6f}")

    assert vals[1] == Fraction(1, 4), vals[1]
    assert vals[2] == Fraction(0), vals[2]
    assert vals[3] == Fraction(1, 8), vals[3]
    assert vals[1] != vals[3], "p(T=1) must differ from p(T=3)"

    # Right-hand side of the conjecture at these endpoints:
    #   GUE ordered-eigenvalue joint density at (1, 3)  times
    #   Vandermonde factor (y2-y1)-(x2-x1) = (3-1)-(4-0) = -2.
    # It has no T-dependence: a single nonzero constant c (in fact c < 0 under the
    # literal reading, while p_n >= 0).  LHS takes distinct values 1/4, 0, 1/8.
    vand = (END[1] - END[0]) - (START[1] - START[0])
    print(f"Vandermonde factor = {vand} (nonzero); RHS is T-free, LHS varies with T")
    print("p(1)=1/4 != 1/8=p(3) at identical endpoints  ->  conjecture 00000000499 is FALSE")
    print("ALL CHECKS PASSED")


if __name__ == "__main__":
    main()
