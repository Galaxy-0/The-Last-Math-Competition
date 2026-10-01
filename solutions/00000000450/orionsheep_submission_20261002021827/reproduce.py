#!/usr/bin/env python3
"""
Standalone exact recomputation for TLMC conjecture 00000000450 (disproof).

No third-party dependencies; pure integer arithmetic.

Conjecture (as stated in conjectures/00000000450.md):
    For the q,t-Catalan number C_n(q,t) and every relevant root of unity zeta
    (primitive n-th root of unity):
        C_n(zeta, zeta^{-1}) = (n+1)^((n-1)/2).

Standard reading of C_n(q,t) (cf. neighbouring conjecture 00000000449, which
describes "the q,t-Catalan" as "Haiman's bisymmetric generalization of the
Catalan numbers"): the Haglund/Garsia-Haiman q,t-Catalan in the dinv-area form

    C_n(q,t) = sum_{D in Dyck_n} q^{area(D)} t^{dinv(D)}

where Dyck paths of semilength n are encoded by area sequences
a = (a_1,...,a_n) with a_1 = 0 and 0 <= a_{i+1} <= a_i + 1,

    area(D) = sum_i a_i
    dinv(D) = #{i<j : a_i = a_j} + #{i<j : a_i = a_j + 1}          (primary+secondary dinv)

At q = zeta, t = zeta^{-1} this becomes the exact cyclotomic integer

    C_n(zeta, zeta^{-1}) = sum_D zeta^{area(D) - dinv(D)}.

We evaluate it exactly in Z[zeta]/(Phi_n) and compare with (n+1)^((n-1)/2).

Verdict: the conjecture holds at n = 1 and is FALSE for every n = 2..6:
the true value is exactly -2 (n even) / +2 (n odd), never (n+1)^((n-1)/2).
"""

import math


# ---------------------------------------------------------------- Dyck paths

def area_seqs(n):
    """All area sequences of Dyck paths of semilength n (Catalan many)."""
    out = []

    def rec(prefix):
        if len(prefix) == n:
            out.append(tuple(prefix))
            return
        for v in range(0, prefix[-1] + 2):   # 0 <= v <= prev+1
            rec(prefix + [v])

    rec([0])
    return out


def area(a):
    return sum(a)


def dinv(a):
    d = 0
    for i in range(len(a)):
        for j in range(i + 1, len(a)):
            if a[i] == a[j]:          # primary dinv
                d += 1
            if a[i] == a[j] + 1:      # secondary dinv
                d += 1
    return d


# ------------------------------------------------- exact cyclotomic integers

# Phi_n(x) for n = 1..6 (textbook standard), coefficient lists, index = degree
PHI = {
    1: [-1, 1],           # x - 1
    2: [1, 1],            # x + 1
    3: [1, 1, 1],         # x^2 + x + 1
    4: [1, 0, 1],         # x^2 + 1
    5: [1, 1, 1, 1, 1],   # x^4 + x^3 + x^2 + x + 1
    6: [1, -1, 1],        # x^2 - x + 1
}


def polymod(poly, mod):
    """Reduce integer polynomial (coeff list) modulo monic `mod`, over Z."""
    poly = poly[:]
    md = len(mod) - 1
    for k in range(len(poly) - 1, md - 1, -1):
        c = poly[k]
        if c:
            for i, ci in enumerate(mod):
                poly[k - md + i] -= c * ci
            poly[k] = 0
    while len(poly) > 1 and poly[-1] == 0:
        poly.pop()
    return poly


def poly_str(p):
    return " ".join(f"{c:+d}" if i == 0 else f"{c:+d}*z^{i}"
                    for i, c in enumerate(p) if c) or "0"


def value_exact(n):
    """C_n(zeta, zeta^{-1}) as a vector in Z[zeta]/(Phi_n)."""
    exps = [area(a) - dinv(a) for a in area_seqs(n)]
    acc = [0] * n
    for e in exps:
        acc[e % n] += 1                  # zeta^n = 1
    return polymod(acc, PHI[n])


# ------------------------------------------------------------------- report

def main():
    print("C_n(zeta, zeta^-1) for zeta a primitive n-th root of unity "
          "(exact, in Z[zeta]/(Phi_n))")
    print("claimed value: (n+1)^((n-1)/2)\n")
    results = []
    for n in [1, 2, 3, 4, 5, 6]:
        red = value_exact(n)
        pairs = sorted((area(a), dinv(a)) for a in area_seqs(n))
        is_int = all(c == 0 for c in red[1:])
        val = red[0] if is_int else None
        if n % 2 == 1:
            claim = (n + 1) ** ((n - 1) // 2)
            ok = is_int and val == claim
            print(f"n={n}: C_n monomials (area,dinv) = {pairs}")
            print(f"      value = {poly_str(red)}"
                  f"{'  (= ' + str(val) + ')' if is_int else ''}")
            print(f"      claim = {claim}   ==> {'match' if ok else 'REFUTED'}")
            results.append((n, val, claim, ok))
        else:
            m = n + 1
            s = math.isqrt(m)
            irr = s * s != m
            print(f"n={n}: C_n monomials (area,dinv) = {pairs}")
            print(f"      value = {poly_str(red)}")
            print(f"      claim = {m}^(1/2): "
                  f"{'irrational' if irr else s ** ((n - 1) // 2)}"
                  f"  ==> REFUTED (LHS is the algebraic integer {poly_str(red)})")
            results.append((n, poly_str(red), f"{m}^(1/2)", False))
        print()

    print("--- pipeline verdict anchors ---")
    v2 = sum((-1) ** (area(a) - dinv(a)) for a in area_seqs(2))
    pairs2 = [(area(a), dinv(a)) for a in area_seqs(2)]
    print(f"C_2(q,t) = {' + '.join(f'q^{a}t^{d}' for a, d in pairs2)}"
          f"  (pipeline: 'C2 = q+t') -> {'reproduced' if pairs2 == [(0,1),(1,0)] else 'MISMATCH'}")
    print(f"C_2(-1,-1) = {v2}  (pipeline: -2) -> "
          f"{'reproduced' if v2 == -2 else 'MISMATCH'}")
    exp3 = [area(a) - dinv(a) for a in area_seqs(3)]
    v3 = value_exact(3)[0]
    print(f"n=3 exponents area-dinv = {exp3}; C_3(zeta,zeta^-1) = {v3} "
          f"(pipeline: 2) -> {'reproduced' if v3 == 2 else 'MISMATCH'}")
    print(f"C_3 = 2 != 4 = claim; C_5 = 2 != 36 = claim: integer-level refutations.")
    print(f"sqrt(3) irrationality spot-check (q < 20000): "
          f"{'no p/q with (p/q)^2=3' if not any(math.isqrt(3*q*q)**2 == 3*q*q for q in range(1,20000)) else 'FOUND'}")

    failures = [r for r in results if not r[3]]
    print(f"\nCONCLUSION: conjecture 00000000450 is FALSE "
          f"(refuted at n = {[r[0] for r in failures]}).")
    return 0 if failures else 1


if __name__ == "__main__":
    raise SystemExit(main())
