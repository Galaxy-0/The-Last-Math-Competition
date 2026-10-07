#!/usr/bin/env python3
"""Independent standard-library sanity checks; no numerical result is a proof."""
from math import gcd, log, sqrt


def fib(n):
    a, b = 0, 1
    for _ in range(n):
        a, b = b, a + b
    return a


def stern(n):
    if n == 0:
        return 0
    a, b = 0, 1
    for bit in bin(n)[2:]:
        if bit == '0':
            b = a + b
        else:
            a = a + b
    return a


def digit_length(base, value):
    count = 0
    while value:
        count += 1
        value //= base
    return count


def main():
    phi = (1 + sqrt(5)) / 2
    alpha = log(phi) / log(2)
    bases = (2, 3, 4, 10, 16)
    level = [(1, 1)]
    print('Direct Calkin-Wilf generation and independent Stern comparison:')
    print('level  nodes   max denominator   max binary digits')
    for n in range(18):
        target = fib(n + 2)
        assert len(level) == 2 ** n
        assert all(a > 0 and b > 0 and gcd(a, b) == 1 for a, b in level)
        assert all(max(a, b) <= target and a + b <= fib(n + 3) for a, b in level)
        assert (fib(n + 1), target) in level
        assert (target, fib(n + 1)) in level
        assert max(b for a, b in level) == target
        assert max(b.bit_length() for a, b in level) == target.bit_length()
        for base in bases:
            assert max(digit_length(base, denominator)
                       for denominator in {b for _, b in level}) == digit_length(base, target)
        # Breadth-first order is exactly s(j)/s(j+1), 2^n <= j < 2^(n+1).
        assert all((a, b) == (stern(j), stern(j + 1))
                   for j, (a, b) in enumerate(level, start=2 ** n))
        print(f'{n:5d} {len(level):7d} {target:17d} {target.bit_length():18d}')
        if n < 17:
            level = [child for a, b in level for child in ((a, a + b), (a + b, b))]
    a, b = 1, 1  # F_1, F_2
    max_error = 0.0
    counts = {base: 1 for base in bases}
    next_power = {base: base for base in bases}
    largest_error = {base: 0.0 for base in bases}
    for n in range(10001):
        error = b.bit_length() - n * alpha
        assert -1e-10 < error <= alpha + 1 + 1e-10
        max_error = max(max_error, error)
        for base in bases:
            while b >= next_power[base]:
                counts[base] += 1
                next_power[base] *= base
            assert next_power[base] // base <= b < next_power[base]
            slope = log(phi) / log(base)
            base_error = counts[base] - n * slope
            assert -1e-10 < base_error <= slope + 1 + 1e-10
            largest_error[base] = max(largest_error[base], base_error)
            if base >= 3:
                binary_error = abs(counts[base] - n * alpha)
                assert binary_error + 1e-10 >= n * (alpha - slope) - (slope + 1)
                if n in (100, 1000, 10000):
                    print(f'base={base}, n={n}: digits={counts[base]}, error against binary coefficient={binary_error:.9f}')
        a, b = b, a + b
    print(f'Binary slope log_2(phi) = {alpha:.15f}')
    print(f'Explicit proven bound log_2(phi)+1 = {alpha + 1:.15f}')
    print(f'Largest observed error through level 10000 = {max_error:.15f}')
    print('PASS: exact level maxima for bases 2, 3, 4, 10, 16 through level 17.')
    for base in bases:
        slope = log(phi) / log(base)
        print(f'base={base}: slope={slope:.15f}, explicit bound={slope+1:.15f}, largest observed base error={largest_error[base]:.15f}')
    print('ALL CHECKS PASSED (finite sanity checks, supplementary to Lean proof).')


if __name__ == '__main__':
    main()
