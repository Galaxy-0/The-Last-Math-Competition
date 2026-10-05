#!/usr/bin/env python3
"""Independent check for conjecture 00000007964 (Python 3 standard library only).

Words of length n are integers 0 .. 2^n - 1 (bit j = coordinate j).  Unlike the
Lean proof (which reasons with syndromes symbolically), everything here is brute
force: codes are listed explicitly, the minimum distance is the least nonzero
codeword weight, and the covering radius is found by a multi-source BFS on the
hypercube Q_n starting from all codewords.
"""
import sys
from collections import deque

def wt(x):
    return bin(x).count("1")

def span(gens):
    code = {0}
    for g in gens:
        code |= {c ^ g for c in code}
    return code

def is_linear(code):
    return 0 in code and all((a ^ b) in code for a in code for b in code)

def min_dist(code):
    return min(wt(c) for c in code if c)          # linear code: d = least nonzero weight

def covering_radius(code, n):
    dist = [-1] * (1 << n)
    q = deque()
    for c in code:
        dist[c] = 0
        q.append(c)
    while q:
        x = q.popleft()
        for j in range(n):
            y = x ^ (1 << j)
            if dist[y] < 0:
                dist[y] = dist[x] + 1
                q.append(y)
    return max(dist), dist

def qp_data(code, n):
    d = min_dist(code)
    e = (d - 1) // 2
    rho, dist = covering_radius(code, n)
    return d, e, rho, dist

def shortened_hamming(n):
    """{x : XOR of labels 1..n of the 1-positions is 0}, by brute force over all words."""
    code = set()
    for x in range(1 << n):
        s = 0
        for j in range(n):
            if x >> j & 1:
                s ^= j + 1
        if s == 0:
            code.add(x)
    return code

def extended_hamming(m):
    n = 1 << m
    # kernel of the parity-check matrix whose rows are the bits of the labels 0..n-1
    # together with the all-ones row.
    rows = [sum(1 << j for j in range(n) if j >> b & 1) for b in range(m)] + [(1 << n) - 1]
    # basis of the kernel by Gaussian elimination over GF(2)
    return kernel(rows, n)

def kernel(rows, n):
    # reduce rows
    piv = {}
    for r in rows:
        for p, pr in piv.items():
            if r >> p & 1:
                r ^= pr
        if r:
            p = r.bit_length() - 1
            for q in list(piv):
                if piv[q] >> p & 1:
                    piv[q] ^= r
            piv[p] = r
    free = [j for j in range(n) if j not in piv]
    gens = []
    for f in free:
        v = 1 << f
        for p, pr in piv.items():
            if pr >> f & 1:
                v |= 1 << p
        gens.append(v)
    return span(gens)

ok = True
def check(cond, msg):
    global ok
    print(("PASS  " if cond else "FAIL  ") + msg)
    ok = ok and cond

def is_pow2_minus1(n):
    return (n + 1) & n == 0

print("== 1. shortened Hamming codes SH(n), n = 3..16 (brute force)")
for n in range(3, 17):
    C = shortened_hamming(n)
    d, e, rho, _ = qp_data(C, n)
    k = len(C).bit_length() - 1
    expect_qp = not is_pow2_minus1(n)
    good = is_linear(C) and d == 3 and e == 1 and rho == (2 if expect_qp else 1)
    check(good, f"SH({n}) = [{n},{k},{d}] code, e={e}, covering radius {rho} -> "
                + ("quasi-perfect" if rho == e + 1 else "perfect (Hamming)"))

print("== 2. extended Hamming codes EH(m), length 2^m, m = 2,3,4")
for m in (2, 3, 4):
    n = 1 << m
    C = extended_hamming(m)
    d, e, rho, dist = qp_data(C, n)
    check(is_linear(C) and d == 4 and e == 1 and rho == 2,
          f"EH({m}) = [{n},{len(C).bit_length()-1},{d}], e={e}, covering radius {rho} -> quasi-perfect")
    # uniform shells: every word at distance 2 from C has exactly n/2 codewords at distance 2,
    # every word at distance 1 has exactly 1 codeword at distance 1 and 0 at distance 2.
    cw = sorted(C)
    cnt2 = set(); cnt1 = set()
    for x in range(1 << n):
        if dist[x] == 2:
            cnt2.add(sum(1 for c in cw if wt(x ^ c) == 2))
        elif dist[x] == 1:
            cnt1.add((sum(1 for c in cw if wt(x ^ c) == 1), sum(1 for c in cw if wt(x ^ c) == 2)))
    check(cnt2 == {n // 2} and cnt1 == {(1, 0)},
          f"EH({m}) shells uniform: dist-2 words see {cnt2} codewords at distance 2; dist-1 words see {cnt1}")

print("== 3. even-weight codes EW(n), n = 2..14, and their shell distribution")
for n in range(2, 15):
    C = {x for x in range(1 << n) if wt(x) % 2 == 0}
    d, e, rho, dist = qp_data(C, n)
    shells = {sum(1 for c in C if wt(x ^ c) == 1) for x in range(1 << n) if dist[x] == 1} if n <= 10 else {n}
    check(is_linear(C) and d == 2 and e == 0 and rho == 1 and shells == {n},
          f"EW({n}): d={d}, e={e}, covering radius {rho}; each odd word has {shells} codewords at distance 1")

print("== 4. repetition codes of even length n = 2m, n = 2..16")
for n in range(2, 17, 2):
    C = {0, (1 << n) - 1}
    d, e, rho, _ = qp_data(C, n)
    check(d == n and e == n // 2 - 1 and rho == n // 2, f"Rep({n}): d={d}, e={e}, covering radius {rho}")

print("== 5. exhaustive: all binary linear codes of length n <= 7")
def all_subspaces(n):
    seen = {frozenset([0])}
    frontier = [frozenset([0])]
    while frontier:
        new = []
        for S in frontier:
            for v in range(1, 1 << n):
                if v not in S:
                    T = frozenset(S | {s ^ v for s in S})
                    if T not in seen:
                        seen.add(T); new.append(T)
        frontier = new
    return seen
for n in range(0, 8):
    subs = all_subspaces(n)
    qp = []; qp3 = []
    for S in subs:
        if len(S) < 2:
            continue
        d, e, rho, _ = qp_data(S, n)
        if rho == e + 1:
            qp.append(d)
            if d >= 3:
                qp3.append(d)
    msg = (f"n={n}: {len(subs)} linear codes, {len(qp)} quasi-perfect"
           + (f" (d values {sorted(set(qp))}; with d>=3: {len(qp3)})" if qp else ""))
    check((len(qp) > 0) == (n >= 2), msg)

print("== 5b. uniform shell distribution (coset weight distributions depend only on the coset's minimum weight)")
# For a linear code C, the shell counts #{c in C : d(x,c) = j} are the weight distribution of the coset x + C.
# Cosets are identified by an exact coset invariant (syndrome); words are bucketed by it.
from collections import Counter, defaultdict
def lab_synd(x, labels):
    s = 0
    for j, l in enumerate(labels):
        if x >> j & 1:
            s ^= l
    return s
def coset_profiles(n, key):
    buckets = defaultdict(Counter)
    for x in range(1 << n):
        buckets[key(x)][wt(x)] += 1
    by_min = defaultdict(set)
    for dist_counter in buckets.values():
        mn = min(dist_counter)
        by_min[mn].add(tuple(sorted(dist_counter.items())))
    return by_min
def uniform(by_min):
    return all(len(v) == 1 for v in by_min.values())
def describe(by_min):
    return "; ".join(f"min wt {r}: {len(v)} distinct profile(s)" for r, v in sorted(by_min.items()))
for m in (3, 4):
    n = (1 << m) - 2
    prof = coset_profiles(n, lambda x: lab_synd(x, range(1, n + 1)))
    check(uniform(prof) and sorted(prof) == [0, 1, 2],
          f"SH({n}) = SH(2^{m}-2) is shell-uniform ({describe(prof)})")
for m in (2, 3, 4):
    n = 1 << m
    prof = coset_profiles(n, lambda x: (lab_synd(x, range(n)), wt(x) % 2))
    check(uniform(prof) and sorted(prof) == [0, 1, 2], f"EH({m}) (length {n}) is shell-uniform ({describe(prof)})")
for n in range(2, 13):
    prof = coset_profiles(n, lambda x: wt(x) % 2)
    check(uniform(prof), f"EW({n}) is shell-uniform ({describe(prof)})")
unif = [n for n in range(3, 15) if uniform(coset_profiles(n, lambda x: lab_synd(x, range(1, n + 1))))]
check(unif == [3, 6, 7, 14],
      f"among SH(n), 3<=n<=14, exactly n in {unif} are shell-uniform (2^m-1: perfect; 2^m-2: once shortened)")
prof5 = coset_profiles(5, lambda x: lab_synd(x, range(1, 6)))
check(not uniform(prof5), f"SH(5) is quasi-perfect but NOT shell-uniform ({describe(prof5)}), cf. Lean SH5_not_shellUniform")

print("== 6. the bit lemma: 2^k <= s < 2^(k+1)  =>  s xor 2^k < 2^k  (k <= 12)")
check(all((s ^ (1 << k)) < (1 << k) for k in range(13) for s in range(1 << k, 1 << (k + 1))),
      "bit lemma")

print("== 7. lengths outside {2^k - 1} carrying QP codes with d = 3 (SH) up to 64")
outside = [n for n in range(3, 65) if not is_pow2_minus1(n)]
print("      ", len(outside), "lengths:", outside[:12], "...")

print()
print("ALL CHECKS PASSED" if ok else "SOME CHECK FAILED")
sys.exit(0 if ok else 1)
