#!/usr/bin/env python3
"""Independent standard-library checks; Lean supplies the proof for all indices."""


def product_coefficients(k):
    result = [1]
    for i in range(k):
        step = 1 << i
        new = [0] * (len(result) + step)
        for n, value in enumerate(result):
            new[n] += value
            new[n + step] += value
        result = new
    return result


def partitions(n, largest=None):
    """Enumerate unordered partitions using powers of two, repetitions allowed."""
    if n == 0:
        return [()]
    if largest is None:
        largest = 1 << (n.bit_length() - 1)
    if largest == 0:
        return []
    result = []
    for multiplicity in range(n // largest + 1):
        for tail in partitions(n - multiplicity * largest, largest // 2):
            result.append((largest,) * multiplicity + tail)
    return result


def binary_counts(limit):
    counts = [1] + [0] * limit
    part = 1
    while part <= limit:
        for n in range(part, limit + 1):
            counts[n] += counts[n - part]
        part *= 2
    return counts


def main():
    for k in range(11):
        coefficients = product_coefficients(k)
        assert len(coefficients) == 2**k
        assert coefficients == [1] * (2**k)
    print('Truncated products K = 0,...,10: all coefficients below 2^K are 1.')
    counts = binary_counts(64)
    for n in range(33):
        enumerated = partitions(n)
        assert len(enumerated) == len(set(enumerated)) == counts[n]
        assert all(sum(p) == n for p in enumerated)
    assert counts[:9] == [1, 1, 2, 2, 4, 4, 6, 6, 10]
    assert set(partitions(2)) == {(2,), (1, 1)}
    assert counts[4] == 4
    print('Binary partition counts n = 0,...,8:', counts[:9])
    print('The partitions of 2:', sorted(partitions(2)))
    print('The partitions of 4:', sorted(partitions(4)))
    for k in range(2, 11):
        assert product_coefficients(k)[2] == 1 != counts[2] == 2
    print('Mismatch at degree 2: stable product coefficient = 1; b(2) = 2.')
    print('ALL CHECKS PASSED')


if __name__ == '__main__':
    main()
