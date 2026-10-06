#!/usr/bin/env python3
"""Exact, standalone auxiliary checks for the literal table in conjecture 407.

Python standard library only. Output is deterministic JSON on stdout.
The source-table loop deliberately does not use a degree-vanishing shortcut.
Finite checks are not a proof of an asymptotic statement.

Primary definition references (accessed 2026-10-05):
* Gutschwager (2008), section 2, p. 2: conventional LR tableaux.
  https://www.combinatorics.org/ojs/index.php/eljc/article/download/v15i1n30/pdf/
* van Leeuwen (2006), equation (39), p. 24: Jacobi--Trudi.
  https://www.combinatorics.org/ojs/index.php/eljc/article/download/v11i2a5/pdf/
* Stembridge (2002), bi-alternant corollary, p. 3.
  https://www.combinatorics.org/ojs/index.php/eljc/article/download/v9i1n5/pdf
"""

from collections import Counter
from functools import lru_cache
from itertools import permutations, product
import hashlib
import json
from pathlib import Path


SOURCE_TABLE_MAX_N = 10
ALGEBRA_MAX_TOTAL = 6


@lru_cache(maxsize=None)
def partitions(n, ceiling=None):
    """Every partition of n once, as a decreasing tuple of positive parts."""
    if ceiling is None:
        ceiling = n
    if n == 0:
        return ((),)
    return tuple(
        (first,) + tail
        for first in range(min(n, ceiling), 0, -1)
        for tail in partitions(n - first, first)
    )


def valid_partition(parts):
    return all(type(x) is int and x > 0 for x in parts) and all(
        a >= b for a, b in zip(parts, parts[1:])
    )


def lr_tableaux(lam, mu, nu):
    """Enumerate tableaux of nu/lam and exact content mu.

    Coordinates are zero-based, in English/matrix orientation. Labels start
    at one. Read right-to-left in successive rows from top to bottom. Every
    prefix has at least as many i's as (i+1)'s. Rows are weakly increasing
    left-to-right and columns strictly increasing top-to-bottom.

    No test of |lam|+|mu|=|nu| is made: exact content is checked at the end.
    Missing containment is assigned coefficient zero, as usual.
    """
    if not all(valid_partition(p) for p in (lam, mu, nu)):
        raise ValueError("Inputs must be canonical partitions")
    if any(i >= len(nu) or v > nu[i] for i, v in enumerate(lam)):
        return
    cells = tuple(
        (r, c)
        for r, width in enumerate(nu)
        for c in range(width - 1, (lam[r] if r < len(lam) else 0) - 1, -1)
    )
    placed = {}
    used = [0] * len(mu)

    def visit(pos):
        if pos == len(cells):
            if tuple(used) == mu:
                yield tuple((r, c, placed[r, c]) for r, c in cells)
            return
        r, c = cells[pos]
        for label in range(1, len(mu) + 1):
            k = label - 1
            if used[k] == mu[k]:
                continue
            if (r, c + 1) in placed and label > placed[r, c + 1]:
                continue
            if (r - 1, c) in placed and label <= placed[r - 1, c]:
                continue
            used[k] += 1
            if all(used[j] >= used[j + 1] for j in range(len(used) - 1)):
                placed[r, c] = label
                yield from visit(pos + 1)
                del placed[r, c]
            used[k] -= 1

    yield from visit(0)


def lr(lam, mu, nu):
    return sum(1 for _ in lr_tableaux(lam, mu, nu))


def polynomial_multiply(a, b):
    """Sparse integer polynomials: exponent tuple -> integer coefficient."""
    result = Counter()
    for left, x in a.items():
        for right, y in b.items():
            exponent = tuple(u + v for u, v in zip(left, right))
            result[exponent] += x * y
    return {exponent: value for exponent, value in result.items() if value}


@lru_cache(maxsize=None)
def weak_compositions(total, variables):
    if variables == 1:
        return ((total,),)
    return tuple(
        (head,) + tail
        for head in range(total + 1)
        for tail in weak_compositions(total - head, variables - 1)
    )


@lru_cache(maxsize=None)
def complete_homogeneous(degree, variables):
    if degree < 0:
        return {}
    return {exponent: 1 for exponent in weak_compositions(degree, variables)}


def permutation_sign(perm):
    inversions = sum(
        perm[i] > perm[j]
        for i in range(len(perm))
        for j in range(i + 1, len(perm))
    )
    return (-1) ** inversions


@lru_cache(maxsize=None)
def schur_jacobi_trudi(shape, variables):
    """Independent of all tableau code: det(h_{shape[i]-i+j})."""
    result = Counter()
    one = {(0,) * variables: 1}
    for perm in permutations(range(len(shape))):
        degrees = tuple(shape[i] - i + perm[i] for i in range(len(shape)))
        if any(degree < 0 for degree in degrees):
            continue
        term = one
        for degree in degrees:
            term = polynomial_multiply(term, complete_homogeneous(degree, variables))
        sign = permutation_sign(perm)
        for exponent, coefficient in term.items():
            result[exponent] += sign * coefficient
    return {exponent: value for exponent, value in result.items() if value}


@lru_cache(maxsize=None)
def denominator_alternant(variables):
    """Exponent/sign pairs for det(x_i ** (variables-1-j))."""
    return tuple(
        (tuple(variables - 1 - perm[i] for i in range(variables)), permutation_sign(perm))
        for perm in permutations(range(variables))
    )


def schur_product_coefficient(poly, nu, variables):
    """[x^(nu+delta)] (a_delta * poly), using the bi-alternant formula.

    Distinct decreasing exponent vectors nu+delta occur in exactly one
    alternant a_(nu+delta), with coefficient +1. Here variables >= total
    product degree, so all relevant partitions fit. No tableau code is used.
    """
    if len(nu) > variables:
        raise ValueError("Too few variables for this target")
    target = tuple(
        (nu[i] if i < len(nu) else 0) + variables - 1 - i
        for i in range(variables)
    )
    answer = 0
    for exponent, sign in denominator_alternant(variables):
        difference = tuple(a - b for a, b in zip(target, exponent))
        if min(difference) >= 0:
            answer += sign * poly.get(difference, 0)
    return answer


def conjugate(shape):
    return tuple(sum(row > column for row in shape) for column in range(max(shape, default=0)))


def filling_conditions(lam, mu, nu, entries):
    """A full-assignment validator, independent of backtracking/pruning.

    Compare every pair in each row/column, then examine completed prefixes.
    This function is used only to isolate malformed fillings in sanity tests.
    """
    filling = {(r, c): label for r, c, label in entries}
    expected_cells = {
        (r, c) for r, width in enumerate(nu)
        for c in range(lam[r] if r < len(lam) else 0, width)
    }
    word = [filling[cell] for cell in sorted(filling, key=lambda rc: (rc[0], -rc[1]))]
    prefix_counts = [Counter(word[:stop]) for stop in range(len(word) + 1)]
    return dict(
        cells=len(filling) == len(entries) and set(filling) == expected_cells,
        positive_labels=all(label > 0 for label in filling.values()),
        content=Counter(filling.values()) == Counter({i + 1: v for i, v in enumerate(mu)}),
        rows=all(x <= y for (r, c), x in filling.items() for (s, d), y in filling.items()
                 if r == s and c < d),
        columns=all(x < y for (r, c), x in filling.items() for (s, d), y in filling.items()
                    if c == d and r < s),
        lattice=all(count[i] >= count[i + 1]
                    for count in prefix_counts for i in range(1, max(word, default=0))),
    )


def isolated_filling_cases():
    good = ((0, 2, 1), (0, 1, 1), (1, 1, 2), (1, 0, 1))
    cases = [
        ("valid with row and column constraints", (1,), (3, 1), (3, 2), good, None),
        ("only row condition fails", (2, 1), (2, 1, 1), (4, 3),
         ((0, 3, 1), (0, 2, 1), (1, 2, 2), (1, 1, 3)), "rows"),
        ("only column condition fails", (1,), (3,), (2, 2),
         ((0, 1, 1), (1, 1, 1), (1, 0, 1)), "columns"),
        ("only reading word condition fails", (1,), (1, 1), (3,),
         ((0, 2, 2), (0, 1, 1)), "lattice"),
        ("only exact content condition fails", (1,), (2, 2), (3, 2), good, "content"),
    ]
    output = []
    for name, lam, mu, nu, entries, failure in cases:
        conditions = filling_conditions(lam, mu, nu, entries)
        assert {key for key, value in conditions.items() if not value} == (
            set() if failure is None else {failure}
        ), (name, conditions)
        accepted = entries in set(lr_tableaux(lam, mu, nu))
        assert accepted == (failure is None), (name, accepted)
        output.append(dict(name=name, lambda_=lam, mu=mu, nu=nu,
                           filling=entries, conditions=conditions, accepted=accepted))
    return output


def named_sanity_cases():
    # Expected numbers chosen before invoking the implementation. In the two
    # Pieri-negative cases the shapes contain lam and the sizes do add up.
    cases = [
        ("empty unit", (), (), (), 1),
        ("left unit", (), (2, 1), (2, 1), 1),
        ("right unit", (2, 1), (), (2, 1), 1),
        ("horizontal Pieri positive", (2,), (2,), (3, 1), 1),
        ("horizontal Pieri column obstruction", (2,), (2,), (2, 1, 1), 0),
        ("vertical Pieri positive", (2,), (1, 1), (3, 1), 1),
        ("vertical Pieri row obstruction", (2,), (1, 1), (4,), 0),
        ("unequal input sizes positive", (2, 1), (2,), (3, 1, 1), 1),
        ("unequal input sizes column obstruction", (2, 1), (2,), (2, 1, 1, 1), 0),
        ("multiplicity two", (2, 1), (2, 1), (3, 2, 1), 2),
        ("missing containment", (2,), (1,), (1, 1, 1), 0),
        ("too much requested content", (1,), (2,), (2,), 0),
        ("too little requested content", (1,), (1,), (3,), 0),
        ("nonempty content in empty skew shape", (1,), (1,), (1,), 0),
    ]
    result = []
    variables = ALGEBRA_MAX_TOTAL
    for name, lam, mu, nu, expected in cases:
        observed = lr(lam, mu, nu)
        poly = polynomial_multiply(schur_jacobi_trudi(lam, variables), schur_jacobi_trudi(mu, variables))
        algebra = schur_product_coefficient(poly, nu, variables)
        assert observed == algebra == expected, (name, observed, algebra, expected)
        result.append(dict(name=name, lambda_=lam, mu=mu, nu=nu, expected=expected,
                           tableau_count=observed, schur_coefficient=algebra))
    return result


def source_table():
    rows = []
    for n in range(SOURCE_TABLE_MAX_N + 1):
        shapes = partitions(n)
        histogram = Counter(lr(lam, mu, nu) for lam, mu, nu in product(shapes, repeat=3))
        assert sum(histogram.values()) == len(shapes) ** 3
        rows.append(dict(n=n, partitions=len(shapes), entries=sum(histogram.values()),
                         nonzero_entries=sum(count for value, count in histogram.items() if value),
                         coefficient_histogram=dict(sorted(histogram.items()))))
    assert rows[0]["nonzero_entries"] == 1
    assert all(row["nonzero_entries"] == 0 for row in rows[1:])
    return rows


def independent_cross_check():
    """All |lam|+|mu|<=6 and |nu|<=6, including mismatched degrees."""
    variables = ALGEBRA_MAX_TOTAL
    targets = tuple(p for n in range(variables + 1) for p in partitions(n))
    checked = compatible = positive = nontrivial_zero = mismatch = 0
    histogram = Counter()
    pair_count = 0
    for total in range(variables + 1):
        for a in range(total + 1):
            for lam in partitions(a):
                for mu in partitions(total - a):
                    pair_count += 1
                    poly = polynomial_multiply(
                        schur_jacobi_trudi(lam, variables),
                        schur_jacobi_trudi(mu, variables),
                    )
                    for nu in targets:
                        tableau = lr(lam, mu, nu)
                        algebra = schur_product_coefficient(poly, nu, variables)
                        assert tableau == algebra, (lam, mu, nu, tableau, algebra)
                        assert tableau == lr(mu, lam, nu), ("commutativity", lam, mu, nu)
                        assert tableau == lr(conjugate(lam), conjugate(mu), conjugate(nu)), (
                            "conjugation", lam, mu, nu)
                        checked += 1
                        if sum(nu) == total:
                            compatible += 1
                            histogram[tableau] += 1
                            positive += tableau > 0
                            nontrivial_zero += tableau == 0
                        else:
                            mismatch += 1
                            assert tableau == 0
    return dict(max_total_input_size=variables, max_output_size=variables,
                variables=variables, input_pairs=pair_count, triples_checked=checked,
                degree_compatible_triples=compatible, positive_coefficients=positive,
                degree_compatible_zero_coefficients=nontrivial_zero,
                degree_mismatched_triples=mismatch,
                degree_compatible_histogram=dict(sorted(histogram.items())),
                schur_disagreements=0, commutativity_disagreements=0,
                conjugation_disagreements=0)


def main():
    # Independent, familiar partition counts check the source-table index set.
    expected_partition_counts = (1, 1, 2, 3, 5, 7, 11, 15, 22, 30, 42)
    assert tuple(len(partitions(n)) for n in range(11)) == expected_partition_counts
    sanity = named_sanity_cases()
    isolated = isolated_filling_cases()
    table = source_table()
    cross = independent_cross_check()
    witnesses = list(lr_tableaux((2, 1), (2, 1), (3, 2, 1)))
    result = dict(
        candidate="00000000407",
        script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        status="all checks passed",
        arithmetic="exact Python integers; standard library only",
        source_indexing="lambda, mu, nu are all partitions of the same n",
        tableau_degree_shortcut=False,
        finite_experiments_only=True,
        source_table=table,
        named_sanity_cases=sanity,
        isolated_filling_cases=isolated,
        independent_schur_check=cross,
        multiplicity_two_witnesses=dict(lambda_=[2, 1], mu=[2, 1], nu=[3, 2, 1],
                                        coordinates="zero-based row, column, positive label; reading order",
                                        tableaux=witnesses),
    )
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
