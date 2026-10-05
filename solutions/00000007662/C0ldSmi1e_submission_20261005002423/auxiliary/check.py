#!/usr/bin/env python3
"""Exact bounded checks of the printed functional equation for conjecture 7662.

Standard library only. All arithmetic is integral. Finite checks supplement the
Lean proof and make no inference about untested indices or probable primes.
"""
import argparse
import hashlib
import json
from pathlib import Path

if not __debug__:
    raise RuntimeError('This verifier requires assertions; do not use Python optimization.')


def multiply(left, right):
    assert len(left) == len(right)
    result = [0] * len(left)
    for i, value in enumerate(left):
        for j in range(len(left) - i):
            result[i + j] += value * right[j]
    return result


def unit_inverse(series):
    assert series[0] == 1
    result = [1] + [0] * (len(series) - 1)
    for degree in range(1, len(series)):
        result[degree] = -sum(series[i] * result[degree - i]
                              for i in range(1, degree + 1))
    assert multiply(series, result) == [1] + [0] * (len(series) - 1)
    return result


def shift(series):
    return [0] + series[:-1]


def literal_quotient(series, q):
    # Build (1 - q*t*F(q*t)) / (1 - t*F(t)) using separate series operations.
    substituted = [value * q ** i for i, value in enumerate(series)]
    numerator = [-q * value for value in shift(substituted)]
    numerator[0] += 1
    denominator = [-value for value in shift(series)]
    denominator[0] += 1
    return multiply(numerator, unit_inverse(denominator))


def quotient_fixed_point(q, degree):
    result = [0] * (degree + 1)
    # Each iterate fixes one further coefficient because each occurrence of F
    # is multiplied by t before it affects the numerator or denominator.
    for iteration in range(degree + 1):
        new = literal_quotient(result, q)
        assert new[:iteration] == result[:iteration]
        result = new
    assert literal_quotient(result, q) == result
    return result


def triangular_coefficients(q, degree):
    # From F - t*F^2 = 1 - q*t*F(q*t), independently by coefficient extraction.
    result = [1]
    for n in range(1, degree + 1):
        result.append(sum(result[i] * result[n - 1 - i] for i in range(n))
                      - q ** n * result[n - 1])
    return result


def audit(q, degree):
    recurrence = triangular_coefficients(q, degree)
    quotient = quotient_fixed_point(q, degree)
    assert recurrence == quotient
    assert literal_quotient(recurrence, q) == recurrence
    left = [a - b for a, b in zip(recurrence, shift(multiply(recurrence, recurrence)))]
    right = [-q * value for value in shift([a * q ** n for n, a in enumerate(recurrence)])]
    right[0] += 1
    assert left == right
    record = {'q': q, 'degree': degree, 'coefficient_count': degree + 1,
              'methods_agree': True, 'original_quotient_identity': True,
              'cross_multiplied_identity': True, 'coefficients': recurrence}
    if q == 2:
        assert recurrence[:6] == [1, -1, 2, -11, 150, -4474]
        assert all(value < 0 for n, value in enumerate(recurrence) if n % 2 == 1)
        assert all(value % 2 == 0 for n, value in enumerate(recurrence) if n > 0 and n % 2 == 0)
        assert all(value >= 4 for n, value in enumerate(recurrence) if n >= 4 and n % 2 == 0)
        record['bounded_sign_and_evenness_checks'] = True
        record['bounded_prime_index_classification'] = [2]
        record['classification_method'] = ('At n=0 value 1; at n=2 value 2. Odd-index values '
            'are negative; every other positive even-index value is even and at least 4. '
            'No probable-prime test or classification beyond the tested range is used.')
    return record


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--degree', type=int, default=32)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    if args.degree < 5:
        parser.error('--degree must be at least 5')
    records = [audit(q, args.degree) for q in (-2, -1, 0, 1, 2, 3, 4)]
    result = {'status': 'PASS', 'problem': '00000007662', 'degree': args.degree,
              'parameter_count': len(records), 'coefficient_comparisons': sum(r['coefficient_count'] for r in records),
              'arithmetic': 'exact Python integers; no external dependencies',
              'scope': 'Bounded checks only; this program makes no claim about untested indices.',
              'checker_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              'cases': records}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(f"PASS: {len(records)} parameters, degrees 0..{args.degree}, "
          f"{result['coefficient_comparisons']} exact coefficient comparisons.")
    print('At q=2 the only index with a positive prime coefficient in the tested range is 2.')


if __name__ == '__main__':
    main()
