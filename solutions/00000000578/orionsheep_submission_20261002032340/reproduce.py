"""reproduce.py: independent recomputation of the attack numbers for
TLMC conjecture 00000000578.

Run:  python3 reproduce.py
Requires: Python 3.8+ only (standard library).

The script computes the characteristic polynomial of the binomial matroid
bin(n,i) -- the matroid on the i-subsets of {1..n} represented over GF(2) by
weight-i 0/1 vectors -- directly from the rank formula

    chi_M(t) = sum_{X subseteq E} (-1)^{|X|} t^{r(E) - r(X)}.

The GF(2) rank is computed by two *independent* implementations (Gaussian
elimination and brute-force span enumeration), which are cross-checked on
every subset used.  All expected attack numbers are asserted.
"""

from itertools import combinations
from math import factorial

# ---------------------------------------------------------------- GF(2) rank

def rank_gauss(vectors):
    """GF(2) rank via echelon insertion (bitmasks)."""
    basis = []
    for v in vectors:
        for b in basis:
            if v & b and (v ^ b) < v:
                v ^= b
        # keep basis with distinct leading bits
        if v:
            basis = sorted(basis + [v], reverse=True)
    return len(basis)


def rank_span(vectors):
    """GF(2) rank via brute-force span enumeration (independent check)."""
    span = {0}
    for v in vectors:
        span |= {x ^ v for x in span}
    n = len(span)
    assert n & (n - 1) == 0, "span size must be a power of 2"
    return n.bit_length() - 1


# ------------------------------------------------------- characteristic poly

def char_poly(n, i):
    """Characteristic polynomial of bin(n,i) as {degree: coeff}."""
    E = []
    for S in combinations(range(n), i):
        m = 0
        for j in S:
            m |= 1 << j
        E.append(m)
    rE = rank_gauss(E)
    assert rE == rank_span(E)
    coeffs = {}
    N = len(E)
    assert N <= 16, "brute force limited to |E| <= 16"
    for mask in range(1 << N):
        X = [E[k] for k in range(N) if (mask >> k) & 1]
        rX = rank_gauss(X) if X else 0
        assert rX == (rank_span(X) if X else 0)
        deg = rE - rX
        sign = -1 if len(X) % 2 else 1
        coeffs[deg] = coeffs.get(deg, 0) + sign
    return rE, coeffs


def eval_poly(coeffs, t):
    return sum(c * t ** d for d, c in coeffs.items())


def poly_str(coeffs):
    terms = []
    for d in sorted(coeffs, reverse=True):
        c = coeffs[d]
        if c:
            terms.append(f"{c:+d}t^{d}" if d else f"{c:+d}")
    return "".join(terms).lstrip("+")


def check(n, i, m, expected, modulus_expected):
    rE, c = char_poly(n, i)
    val = eval_poly(c, -m)
    modulus = factorial(i) * factorial(n - i)
    ok = val % modulus == 0
    print(f"bin({n},{i}): r={rE}  chi(t) = {poly_str(c)}")
    print(f"  chi(-{m}) = {val};  i!(n-i)! = {modulus};  "
          f"remainder = {val % modulus};  divisible = {ok}")
    assert rE == modulus_expected[0]
    assert val == expected
    assert not ok
    return val


def boundary(n, i, ms):
    rE, c = char_poly(n, i)
    modulus = factorial(i) * factorial(n - i)
    return {m: eval_poly(c, -m) % modulus == 0 for m in ms}


if __name__ == "__main__":
    print("=== Attack 1: bin(5,3), m=1, modulus 3!*2! = 12 ===")
    check(5, 3, 1, expected=-332, modulus_expected=(5,))

    print()
    print("=== Attack 2: bin(6,2), m=2, modulus 2!*4! = 48 ===")
    check(6, 2, 2, expected=-2520, modulus_expected=(5,))

    print()
    print("=== Boundary sweep (divisible?) ===")
    for (n, i) in [(4, 2), (5, 2), (5, 3), (6, 2)]:
        res = boundary(n, i, [1, 2, 3])
        pretty = ", ".join(f"m={m}:{'OK' if ok else 'FAIL'}" for m, ok in res.items())
        print(f"bin({n},{i}): {pretty}")

    b = boundary(5, 3, [1, 2, 3])
    assert b == {1: False, 2: False, 3: True}
    b = boundary(6, 2, [1, 2, 3])
    assert b == {1: True, 2: False, 3: True}
    b = boundary(4, 2, [1, 2, 3])
    assert b == {1: True, 2: True, 3: True}
    b = boundary(5, 2, [1, 2, 3])
    assert b == {1: True, 2: True, 3: True}

    print()
    print("All assertions passed: conjecture 00000000578 is FALSE.")
