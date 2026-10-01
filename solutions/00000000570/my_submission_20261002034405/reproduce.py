#!/usr/bin/env python3
"""Independent recomputation of the disproof of TLMC conjecture 00000000570.

Kronecker cluster algebra (rank 2, B = [[0,2],[-2,0]], affine A1, acyclic).
Cluster variables in the initial cluster (x1, x2) satisfy
    x_{n+1} * x_{n-1} = x_n^2 + 1,
and by the Laurent phenomenon each x_n is a Laurent polynomial in x1, x2.
The x1-exponent of the support of x_n spans [-(n-2), n-4], i.e. the width
is 2(n-3): 0, 2, 4, 6, 8, 10, 12, ... for n = 3, 4, ..., -- unbounded,
violating the conjectured bound 2*rank = 4 from x6 on.

Pure Python, no dependencies.  Exact greedy Laurent-polynomial division with
verification by remultiplication; the seven exchange identities are asserted
exactly as Laurent-polynomial equalities.
"""
from collections import defaultdict


def norm(d):
    return {k: v for k, v in d.items() if v != 0}


def mul(p, q):
    r = defaultdict(int)
    for (a, b), c in p.items():
        for (d, e), f in q.items():
            r[(a + d, b + e)] += c * f
    return norm(r)


def add(p, q):
    r = defaultdict(int, p)
    for k, v in q.items():
        r[k] += v
    return norm(r)


def ldiv(n, d):
    """Greedy exact division of Laurent polynomial n by d (lex order)."""
    q = defaultdict(int)
    n = dict(n)
    dl = max(d)
    dc = d[dl]
    while n:
        nl = max(n)
        t = (nl[0] - dl[0], nl[1] - dl[1])
        num = n[nl]
        assert num % dc == 0, "coefficient divisibility"
        qt = num // dc
        q[t] += qt
        if q[t] == 0:
            del q[t]
        for (a, b), c in d.items():
            k = (t[0] + a, t[1] + b)
            n[k] = n.get(k, 0) - qt * c
            if n[k] == 0:
                del n[k]
    return norm(q)


X1 = {(1, 0): 1}
X2 = {(0, 1): 1}
N = 26
xs = [None, X1, X2]
for n in range(3, N):
    num = add(mul(xs[n - 1], xs[n - 1]), {(0, 0): 1})
    q = ldiv(num, xs[n - 2])
    assert mul(q, xs[n - 2]) == num, f"division check failed at n={n}"
    xs.append(q)

# exact verification of all seven exchange relations x_{n-1} x_{n+1} = x_n^2 + 1
for n in range(2, 9):
    prod = mul(xs[n - 1], xs[n + 1])
    sq = add(mul(xs[n], xs[n]), {(0, 0): 1})
    assert prod == sq, f"exchange relation x{n-1}*x{n+1} = x{n}^2 + 1 failed"
print("exchange relations x1*x3 = x2^2+1, ..., x7*x9 = x8^2+1 : all exact")

print("\nn | #terms | x1-range      | width | bound 2*rank = 4")
for n in range(1, N):
    p = xs[n]
    a_range = [k[0] for k in p]
    lo, hi = min(a_range), max(a_range)
    width = hi - lo
    flag = "VIOLATION" if (n >= 3 and width > 4) else "ok"
    print(f"{n:2d} | {len(p):5d}   | [{lo:3d},{hi:3d}]     | {width:5d} | {flag}")

assert [max(k[0] for k in xs[n]) - min(k[0] for k in xs[n]) for n in range(3, 10)] \
    == [0, 2, 4, 6, 8, 10, 12], "attack numbers 0,2,4,6,8,10,12"
assert max(k[0] for k in xs[6]) - min(k[0] for k in xs[6]) == 6 > 4
assert max(k[0] for k in xs[25]) - min(k[0] for k in xs[25]) == 44, "unbounded growth to n=25"
print("\nattack numbers 0,2,4,6,8,10,12 for x3..x9 : confirmed (x6 width 6 > 4)")
print("width(x25) = 44 : unbounded growth confirmed")

print("\nexpansions:")
def show(p):
    return " + ".join(f"{c}*x1^{a}*x2^{b}" for (a, b), c in sorted(p.items()))
for n in range(3, 10):
    print(f"x{n} = {show(xs[n])}")


# boundary: b = 1 (finite type A2) keeps the width <= 4
def widths(b, nmax):
    ys = [None, X1, X2]
    for n in range(3, nmax):
        pw = {(0, 0): 1}
        for _ in range(b):
            pw = mul(pw, ys[n - 1])
        ys.append(ldiv(add(pw, {(0, 0): 1}), ys[n - 2]))
    return [max(k[0] for k in ys[n]) - min(k[0] for k in ys[n]) for n in range(1, nmax)]

w_b1 = widths(1, 16)
w_b2 = widths(2, 16)
print(f"\nboundary b=1 (finite A2) widths x1..x15: {w_b1}  (all <= 1 <= 4: bound holds)")
print(f"boundary b=2 (Kronecker) widths x1..x15: {w_b2}  (unbounded: bound fails)")


# Lean term tables for cross-checking lean4/Main.lean
def wrap(tokens):
    lines, cur = [], ""
    for i, t in enumerate(tokens):
        if not cur:
            cur = t
        elif len(cur) + len(t) + 2 > 68:
            lines.append(cur + ",")
            cur = t
        else:
            cur += ", " + t
    lines.append(cur)
    return lines

print("\nLean tables (must match lean4/Main.lean):")
for n in range(1, 10):
    toks = [f"(({a}, {b}), {c})" for (a, b), c in sorted(xs[n].items())]
    print(f"def TBL{n} : T := [")
    for l in wrap(toks):
        print("  " + l)
    print("]")
for n in range(2, 9):
    ks = sorted(add(mul(xs[n], xs[n]), {(0, 0): 1}))
    toks = [f"({a}, {b})" for a, b in ks]
    print(f"def KEYS{n} : List Key := [")
    for l in wrap(toks):
        print("  " + l)
    print("]")
print("\nAll checks passed.")
