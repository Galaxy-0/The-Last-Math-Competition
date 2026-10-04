"""Independent check for conjecture 00000001102 (Python 3 standard library only).

Method (different from the Lean proof): the R-polynomials are read off from the
Iwahori-Hecke algebra, using
    T_{w^{-1}}^{-1} = q^{-l(w)} * sum_{x <= w} eps_x eps_w R_{x,w}(q) T_x
(Kazhdan-Lusztig 1979, (2.0.a); Humphreys, Reflection Groups and Coxeter Groups, 7.5).
The Hecke algebra of S_n is implemented with Laurent polynomials in q, the
products of the inverses T_s^{-1} = q^{-1} T_s - (1 - q^{-1}) are expanded, and
Bruhat order is computed with the tableau criterion (Lean uses chains of
reflections instead).  We then evaluate every reading of "max R_{x,w}" and compare
with the conjectured value 2^d (1 - 2^{-ceil(d/2)}), d = l(w) - l(x), for S_3
(and S_4 as an extra survey).  The variants eps*R and R-tilde are also checked.
"""

from fractions import Fraction
from itertools import permutations
import sys


def length(w):
    return sum(1 for i in range(len(w)) for j in range(i + 1, len(w)) if w[i] > w[j])


def rmul(w, i):
    """w * s_{i+1}: swap positions i, i+1."""
    w = list(w)
    w[i], w[i + 1] = w[i + 1], w[i]
    return tuple(w)


def bruhat_le(x, w):
    """Tableau criterion (Bjorner-Brenti, Thm 2.6.3)."""
    for i in range(1, len(x)):
        a, b = sorted(x[:i]), sorted(w[:i])
        if any(a[k] > b[k] for k in range(i)):
            return False
    return True


# Laurent polynomials in q: dict exponent -> int
def ladd(a, b, c=1):
    r = dict(a)
    for k, v in b.items():
        r[k] = r.get(k, 0) + c * v
    return {k: v for k, v in r.items() if v}


def lshift(a, s):
    return {k + s: v for k, v in a.items()}


def hecke_mul_s(h, i, n):
    """Right-multiply h = sum_w h_w T_w by T_{s_i}^{-1} = q^{-1} T_s - (1 - q^{-1}) T_e."""
    out = {}

    def acc(w, p):
        if p:
            out[w] = ladd(out.get(w, {}), p)

    for w, p in h.items():
        ws = rmul(w, i)
        # T_w T_s
        if length(ws) > length(w):
            ts = {ws: p}
        else:
            ts = {w: ladd(lshift(p, 1), p, -1), ws: lshift(p, 1)}
        for u, pu in ts.items():
            acc(u, lshift(pu, -1))
        # -(1 - q^{-1}) T_w
        acc(w, ladd(lshift(p, -1), p, -1))
    return {w: p for w, p in out.items() if p}


def reduced_word(w):
    word = []
    while True:
        for i in range(len(w) - 1):
            if w[i] > w[i + 1]:
                word.append(i)
                w = rmul(w, i)
                break
        else:
            return list(reversed(word))  # w = s_{word[0]} ... s_{word[-1]}


def r_polys(n):
    perms = list(permutations(range(1, n + 1)))
    e = tuple(range(1, n + 1))
    R = {}
    for w in perms:
        word = reduced_word(w)
        # w = s_1...s_k  =>  T_{w^{-1}}^{-1} = T_{s_1}^{-1} ... T_{s_k}^{-1}
        h = {e: {0: 1}}
        for i in word:
            h = hecke_mul_s(h, i, n)
        lw = length(w)
        for x in perms:
            p = lshift(h.get(x, {}), lw)  # q^{l(w)} * coefficient
            sign = (-1) ** (length(x) + lw)
            if p:
                assert min(p) >= 0
                deg = max(p)
                R[(x, w)] = [sign * p.get(k, 0) for k in range(deg + 1)]
            else:
                R[(x, w)] = []
    return perms, R


def formula(d):
    return Fraction(2) ** d * (1 - Fraction(1, 2 ** ((d + 1) // 2)))


def ev(p, q):
    return sum(c * q ** k for k, c in enumerate(p))


READINGS = {
    "max coefficient": lambda p: max(p),
    "max |coefficient|": lambda p: max(abs(c) for c in p),
    "sum |coefficients|": lambda p: sum(abs(c) for c in p),
    "leading coefficient": lambda p: p[-1],
    "degree": lambda p: len(p) - 1,
    "number of nonzero terms": lambda p: sum(1 for c in p if c),
    "value at q=2": lambda p: ev(p, 2),
}


def rtilde(p, d):
    """R(q) = q^{d/2} Rt(q^{1/2} - q^{-1/2}); Rt has degree d, parity of d.
    Peel off top terms: coefficient of q^d in q^{d/2} t^k ... use the substitution
    q^{d/2} t^k = q^{(d-k)/2} (q - 1)^k for k = d, d-2, ..."""
    p = list(p) + [0] * (d + 1 - len(p))
    rt = [0] * (d + 1)
    rem = list(p)
    for k in range(d, -1, -2):
        # q^{(d-k)/2} (q-1)^k has top degree (d+k)/2
        top = (d + k) // 2
        c = rem[top]
        rt[k] = c
        poly = [1]
        for _ in range(k):
            poly = [a - b for a, b in zip([0] + poly, poly + [0])]
        shift = (d - k) // 2
        for j, a in enumerate(poly):
            rem[j + shift] -= c * a
    assert all(v == 0 for v in rem), (p, d)
    return rt


def main():
    ok = True
    perms, R = r_polys(3)
    print("S_3 via Hecke algebra: R-polynomials of all pairs x <= w (constant term first)")
    by_d = {}
    for (x, w), p in sorted(R.items()):
        le = bruhat_le(x, w)
        if (p != []) != le:
            print("  Bruhat/R mismatch", x, w); ok = False
        if le:
            d = length(w) - length(x)
            by_d.setdefault(d, set()).add(tuple(p))
    pairs = sum(1 for (x, w) in R if bruhat_le(x, w))
    print("  comparable pairs:", pairs)
    expected = {0: {(1,)}, 1: {(-1, 1)}, 2: {(1, -2, 1)}, 3: {(-1, 2, -2, 1)}}
    for d in sorted(by_d):
        print("  d=%d: %s   conjectured value %s" % (d, sorted(by_d[d]), formula(d)))
    if by_d != expected or pairs != 19:
        ok = False
    print("  e.g. R_{e,s1}=", R[((1, 2, 3), (2, 1, 3))], " R_{e,s1s2}=", R[((1, 2, 3), (2, 3, 1))],
          " R_{e,w0}=", R[((1, 2, 3), (3, 2, 1))])

    print()
    print("Readings of 'max R_{x,w}' in S_3, strict pairs x < w (value per d = 1,2,3; formula 1,2,6):")
    for name, rho in READINGS.items():
        vals = [rho(next(iter(by_d[d]))) for d in (1, 2, 3)]
        fails = [d for d, v in zip((1, 2, 3), vals) if v != formula(d)]
        print("  %-24s %s  fails at d = %s" % (name, vals, fails))
        if not fails:
            ok = False
    # every integer evaluation point: d=1 forces q0 = 2, then d=2 gives 1
    bad = [q0 for q0 in range(-50, 51)
           if all(ev(next(iter(by_d[d])), q0) == formula(d) for d in (1, 2))]
    print("  value at q0, q0 in [-50,50], matching d=1 and d=2:", bad)
    if bad:
        ok = False
    print("  max over integers q of R_{e,s1}(q) = q-1: unbounded (R(100) = %d)" % ev([-1, 1], 100))
    print("  pair x = w: R = 1, formula 0; fails for every reading with rho(1) != 0")

    print()
    print("Variants: eps*R = (-1)^d R and R-tilde (R = q^{d/2} Rt(q^{1/2}-q^{-1/2})), d = 1,2,3:")
    for label, tr in (("eps*R", lambda p, d: [(-1) ** d * c for c in p]),
                      ("R-tilde", lambda p, d: rtilde(p, d))):
        polys = {d: tr(list(next(iter(by_d[d]))), d) for d in (1, 2, 3)}
        print("  %s: %s" % (label, polys))
        for name, rho in READINGS.items():
            vals = [rho(polys[d]) for d in (1, 2, 3)]
            fails = [d for d, v in zip((1, 2, 3), vals) if v != formula(d)]
            print("    %-24s %s  fails at d = %s" % (name, vals, fails))
            if not fails:
                ok = False
        bad = [q0 for q0 in range(-50, 51)
               if all(ev(polys[d], q0) == formula(d) for d in (1, 2, 3))]
        print("    value at q0 matching d=1,2,3 for q0 in [-50,50]:", bad)
        if bad:
            ok = False

    print()
    perms4, R4 = r_polys(4)
    by_d4 = {}
    for (x, w), p in R4.items():
        if (p != []) != bruhat_le(x, w):
            ok = False
        if p:
            by_d4.setdefault(length(w) - length(x), set()).add(tuple(p))
    print("S_4 survey (distinct R per d; for every reading the max over pairs vs formula):")
    for d in sorted(by_d4):
        row = {name: max(rho(list(p)) for p in by_d4[d]) for name, rho in READINGS.items()}
        print("  d=%d formula=%s  #distinct R=%d  %s" % (d, formula(d), len(by_d4[d]), row))

    print()
    print("ALL CHECKS PASSED" if ok else "CHECK FAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
