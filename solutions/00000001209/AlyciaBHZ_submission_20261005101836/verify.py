#!/usr/bin/env python3
"""Independent finite game/mex/Beatty checks; not used by the Lean proof."""
from math import isqrt, sqrt

LIMIT = 100

def move(p, q, t, *, inclusive=False):
    x, y = p
    u, v = q
    difference = abs((x-u)-(y-v))
    diagonal = difference <= t if inclusive else difference < t
    return ((u < x and v == y) or (u == x and v < y) or
            (u < x and v < y and diagonal))

def solve(t, *, inclusive=False):
    losing = set()
    for total in range(2*LIMIT+1):
        for x in range(max(0, total-LIMIT), min(LIMIT, total)+1):
            p = x, total-x
            if not any(move(p, q, t, inclusive=inclusive) for q in losing):
                losing.add(p)
    return losing

def mex_pairs(t, count):
    used = set()
    out = []
    candidate = 0
    for n in range(count):
        while candidate in used:
            candidate += 1
        pair = candidate, candidate+t*n
        out.append(pair)
        used.update(pair)
    return out

if __name__ == '__main__':
    pairs = [(isqrt(2*n*n), isqrt(2*n*n)+2*n) for n in range(LIMIT+1)]
    expected = {p for a,b in pairs for p in [(a,b),(b,a)]
                if p[0] <= LIMIT and p[1] <= LIMIT}
    actual = solve(2)
    assert actual == expected, (actual ^ expected)
    assert mex_pairs(2, LIMIT+1) == pairs
    print(f'PASS: complete game recursion on [0,{LIMIT}]^2 matches exact integer Beatty pairs.')
    print(f'PASS: first {LIMIT+1} mex pairs match a_n = isqrt(2*n*n), b_n = a_n+2*n.')
    # Test the alternative rule directly, without implementing it by a parameter shift.
    inclusive = solve(1, inclusive=True)
    classical = solve(1)
    assert inclusive == actual == expected, inclusive ^ expected
    assert inclusive != classical
    assert (1, 3) in inclusive and (1, 2) in classical
    assert move((2, 1), (0, 0), 1, inclusive=True)
    assert not move((2, 1), (0, 0), 1)
    sorted_inclusive = sorted((a, b) for a, b in inclusive if a <= b)
    assert sorted_inclusive == pairs[:len(sorted_inclusive)]
    last_index = len(sorted_inclusive) - 1
    last_a, last_b = sorted_inclusive[-1]
    print(f'PASS: direct <= convention at t=1 matches strict t=2 on [0,{LIMIT}]^2; differs from classical Wythoff.')
    print('First 10 sorted <= t=1 P-positions:', sorted_inclusive[:10])
    print(f'Box-derived <= t=1 slope: n={last_index}, P=({last_a},{last_b}), a_n/n={last_a/last_index:.9f}, b_n/n={last_b/last_index:.9f}')
    phi = (1+sqrt(5))/2
    for n in (100,1000,10000,1000000):
        an = isqrt(2*n*n)
        assert 0 <= 2*n*n-an*an and (an+1)*(an+1) > 2*n*n
        print(f'<= t=1 (= strict t=2), n={n}: a_n/n={an/n:.9f}; a_n/(phi*n)={an/(phi*n):.9f}')
    print('sqrt(2)=%.12f; phi=%.12f; normalized limit=%.12f' %
          (sqrt(2),phi,sqrt(2)/phi))
    print('ALL CHECKS PASSED. Finite checks are supplementary, not an infinite proof.')
