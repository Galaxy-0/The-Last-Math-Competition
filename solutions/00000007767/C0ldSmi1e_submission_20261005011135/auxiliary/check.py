#!/usr/bin/env python3
"""Exact finite checks only; no infinitude or unbounded-iterate conclusion."""

from collections import Counter
from fractions import Fraction
from math import gcd
import json

ITERATE_BOUND = 12
ROOT_POWER_BOUND = 4
CHECK_COUNT = 0


def require(condition, message):
    """Unaffected by Python optimization."""
    global CHECK_COUNT
    CHECK_COUNT += 1
    if not condition:
        raise RuntimeError(message)


def normalize(poly):
    return {e: c for e, c in poly.items() if c != 0}


def add(left, right):
    result = dict(left)
    for exponent, coefficient in right.items():
        result[exponent] = result.get(exponent, 0) + coefficient
    return normalize(result)


def multiply(left, right):
    result = {}
    for i, a in left.items():
        for j, b in right.items():
            result[i + j] = result.get(i + j, 0) + a * b
    return normalize(result)


def polynomial_power(poly, exponent):
    require(exponent >= 0, "Negative polynomial exponent")
    result = {0: 1}
    factor = poly
    while exponent:
        if exponent % 2:
            result = multiply(result, factor)
        factor = multiply(factor, factor)
        exponent //= 2
    return result


def compose(outer, inner):
    result = {}
    for exponent, coefficient in outer.items():
        term = polynomial_power(inner, exponent)
        result = add(result, {j: coefficient * c for j, c in term.items()})
    return result


def degree(poly):
    cleaned = normalize(poly)
    require(bool(cleaned), "Zero polynomial has no degree in this checker")
    return max(cleaned)


def evaluate(poly, value):
    return sum(c * pow(value, e) for e, c in poly.items())


def polynomial_fixtures():
    x = {1: 1}
    require(normalize({0: 0, 1: 2}) == {1: 2}, "Normalization")
    require(add({0: 1, 1: -1}, {1: 1}) == {0: 1}, "Cancellation")
    require(multiply({}, x) == {}, "Zero multiplication")
    require(
        multiply({0: 1, 1: 1}, {0: -1, 1: 1}) == {0: -1, 2: 1},
        "Mixed multiplication",
    )
    require(
        polynomial_power({0: 1, 1: 1}, 3) == {0: 1, 1: 3, 2: 3, 3: 1},
        "Nonmonomial power",
    )
    require(polynomial_power({}, 0) == {0: 1}, "Zeroth power")
    require(polynomial_power({}, 3) == {}, "Positive power of zero")
    require(
        compose({0: 1, 1: 2, 2: 3}, {0: -1, 2: 1})
        == {0: 2, 2: -4, 4: 3},
        "Mixed composition",
    )
    require(compose(x, {0: -3, 4: 2}) == {0: -3, 4: 2}, "Identity")
    require(compose({}, x) == {}, "Zero outer polynomial")
    require(compose({0: 7, 2: 3}, {}) == {0: 7}, "Zero inner polynomial")
    require(degree({0: 2, 3: 0, 2: 4}) == 2, "Degree fixture")
    require(evaluate({0: 2, 2: -4, 4: 3}, -2) == 34, "Evaluation")


def check_polynomials():
    polynomial_fixtures()
    f, g = {2: 1}, {3: 1}
    require(degree(f) == 2 and degree(g) == 3, "Actual degrees")
    require(degree(f) >= 2 and degree(g) >= 2, "Degree hypotheses")
    fg, gf = compose(f, g), compose(g, f)
    require(fg == gf == {6: 1}, "Exact polynomial commutativity")
    polynomials = {2: [{1: 1}], 3: [{1: 1}]}
    values = {2: [2], 3: [2]}
    rows = []
    for depth in range(ITERATE_BOUND + 1):
        row = {"iterate_index": depth}
        for multiplier, base in ((2, f), (3, g)):
            if depth:
                polynomials[multiplier].append(
                    compose(base, polynomials[multiplier][-1])
                )
                previous = values[multiplier][-1]
                new_value = previous * previous
                if multiplier == 3:
                    new_value *= previous
                values[multiplier].append(new_value)
            actual = polynomials[multiplier][depth]
            expected_exponent = pow(multiplier, depth)
            require(
                actual == {expected_exponent: 1},
                f"Sparse iterate: multiplier={multiplier}, depth={depth}",
            )
            require(degree(actual) == expected_exponent, "Iterate degree")
            require(
                evaluate(actual, 2) == values[multiplier][depth],
                "Sparse evaluation versus direct integer iteration",
            )
            row[f"z{multiplier}_degree"] = degree(actual)
            row[f"z{multiplier}_value_at_2_bit_length"] = (
                values[multiplier][depth].bit_length()
            )
        rows.append(row)
    tested_pairs = 0
    for m in range(1, ITERATE_BOUND + 1):
        for n in range(1, ITERATE_BOUND + 1):
            require(
                polynomials[2][m] != polynomials[3][n],
                f"Matching bounded polynomials: m={m}, n={n}",
            )
            require(
                degree(polynomials[2][m]) != degree(polynomials[3][n]),
                "Matching bounded degrees",
            )
            require(
                values[2][m] != values[3][n],
                "Matching bounded exact values at z=2",
            )
            tested_pairs += 1
    require(tested_pairs == ITERATE_BOUND**2, "Pair count")
    return {
        "coefficient_domain": "integers embedded in complex numbers",
        "f_sparse_terms": [[2, 1]],
        "g_sparse_terms": [[3, 1]],
        "degrees": [degree(f), degree(g)],
        "both_compositions_sparse_terms": sorted(
            [list(term) for term in fg.items()]
        ),
        "iterate_checks_including_identity": rows,
        "no_common_iterate_finite_check": {
            "m_range_inclusive": [1, ITERATE_BOUND],
            "n_range_inclusive": [1, ITERATE_BOUND],
            "pairs_tested": tested_pairs,
            "distinct_polynomials_degrees_and_values_at_2": True,
            "unbounded_nonexistence_proved_here": False,
        },
    }


def projective_power(point, exponent):
    # Fraction t denotes exp(2*pi*i*t); Fraction(0) is 1, not affine zero.
    if point in ("affine_zero", "infinity"):
        return point
    require(isinstance(point, Fraction), "Unknown symbolic point")
    angle = point * exponent
    return angle - angle.numerator // angle.denominator


def exact_root_order_by_addition(angle):
    """Direct finite rational-angle addition, independent of gcd."""
    running = Fraction(0)
    for count in range(1, angle.denominator + 1):
        running += angle
        running -= running.numerator // running.denominator
        if running == 0:
            return count
    raise RuntimeError("Root failed to return within its denominator")


def multiplier_order(multiplier, modulus):
    require(gcd(multiplier, modulus) == 1, "Multiplier is not a unit")
    if modulus == 1:
        return 1
    residue = 1
    for count in range(1, modulus + 1):
        residue = residue * multiplier % modulus
        if residue == 1:
            return count
    raise RuntimeError("Unit failed to return within the finite bound")


def cycles_from_table(table):
    size = len(table)
    require(sorted(table) == list(range(size)), "Table is not a permutation")
    unseen = set(range(size))
    cycles = []
    while unseen:
        start = min(unseen)
        cycle = []
        point = start
        while point in unseen:
            unseen.remove(point)
            cycle.append(point)
            point = table[point]
        require(point == start, "Orbit failed to return to its start")
        cycles.append(cycle)
    flattened = [point for cycle in cycles for point in cycle]
    require(sorted(flattened) == list(range(size)), "Cycle partition")
    return cycles


def check_root_actions():
    rows = []
    primitive_sets = []
    for k in range(1, ROOT_POWER_BOUND + 1):
        modulus = pow(5, k)
        angles = [Fraction(a, modulus) for a in range(modulus)]
        require(len(set(angles)) == modulus, "Distinct roots within modulus")
        exact_orders = []
        for a, angle in enumerate(angles):
            direct_order = exact_root_order_by_addition(angle)
            gcd_order = modulus // gcd(a, modulus)
            require(direct_order == gcd_order, "Root-order comparison")
            exact_orders.append(direct_order)
        primitive = [
            a for a, order in enumerate(exact_orders) if order == modulus
        ]
        require(
            primitive == [a for a in range(modulus) if gcd(a, modulus) == 1],
            "Independent primitive-residue definitions",
        )
        require(len(primitive) == modulus - modulus // 5, "Primitive count")
        primitive_sets.append({angles[a] for a in primitive})
        maps = {}
        periods_by_multiplier = {}
        for multiplier in (2, 3):
            table = [(multiplier * a) % modulus for a in range(modulus)]
            cycles = cycles_from_table(table)
            periods = {}
            for cycle in cycles:
                for i, a in enumerate(cycle):
                    next_a = cycle[(i + 1) % len(cycle)]
                    require(
                        projective_power(angles[a], multiplier)
                        == angles[next_a],
                        "Rational-angle action versus residue cycle",
                    )
                    periods[a] = len(cycle)
            order_lookup = {
                order: multiplier_order(multiplier, order)
                for order in sorted(set(exact_orders))
            }
            for a in range(modulus):
                require(
                    periods[a] == order_lookup[exact_orders[a]],
                    "Cycle period versus multiplicative order",
                )
            primitive_cycles = [
                cycle for cycle in cycles if cycle[0] in primitive
            ]
            require(
                sorted(a for cycle in primitive_cycles for a in cycle)
                == primitive,
                "Primitive-cycle partition",
            )
            for a in primitive:
                require(
                    periods[a] == order_lookup[modulus],
                    "Primitive-root period",
                )
            histogram = Counter(map(len, cycles))
            maps[str(multiplier)] = {
                "cycles": cycles,
                "cycle_length_counts": [
                    [length, histogram[length]] for length in sorted(histogram)
                ],
                "primitive_cycle_count": len(primitive_cycles),
                "primitive_cycle_period": order_lookup[modulus],
                "multiplier_orders_by_root_order": [
                    [order, order_lookup[order]]
                    for order in sorted(order_lookup)
                ],
            }
            periods_by_multiplier[multiplier] = periods
        for point in angles:
            require(
                projective_power(projective_power(point, 2), 3)
                == projective_power(projective_power(point, 3), 2),
                "Commutativity on symbolic root",
            )
        rows.append({
            "k": k,
            "modulus": modulus,
            "root_records_columns": [
                "residue", "exact_root_order", "period_under_2", "period_under_3",
            ],
            "root_records": [
                [a, exact_orders[a], periods_by_multiplier[2][a],
                 periods_by_multiplier[3][a]]
                for a in range(modulus)
            ],
            "primitive_residues": primitive,
            "primitive_count": len(primitive),
            "maps_by_multiplier": maps,
        })
    for i, first in enumerate(primitive_sets):
        for second in primitive_sets[i + 1:]:
            require(first.isdisjoint(second), "Distinct primitive strata")
    all_primitive = set().union(*primitive_sets)
    largest_modulus = pow(5, ROOT_POWER_BOUND)
    largest_roots = {
        Fraction(a, largest_modulus) for a in range(largest_modulus)
    }
    require(
        all_primitive | {Fraction(0)} == largest_roots,
        "Finite primitive strata plus 1 cover largest root set",
    )
    special_points = ["affine_zero", "infinity"]
    special_results = []
    for point in special_points:
        for multiplier in (2, 3):
            require(projective_power(point, multiplier) == point, "Fixed point")
        require(
            projective_power(projective_power(point, 2), 3)
            == projective_power(projective_power(point, 3), 2),
            "Commutativity on special point",
        )
        special_results.append({
            "point": point, "period_under_2": 1, "period_under_3": 1,
        })
    require(Fraction(0) not in special_points, "Root 1 differs from affine zero")
    finite_projective_set = largest_roots | set(special_points)
    for multiplier in (2, 3):
        images = {
            projective_power(point, multiplier)
            for point in finite_projective_set
        }
        require(images == finite_projective_set, "Finite projective closure")
    return {
        "representation": "Fraction a/q symbolically denotes exp(2*pi*i*a/q)",
        "k_range_inclusive": [1, ROOT_POWER_BOUND],
        "cycles_are_residues_modulo_the_stated_modulus": True,
        "cycles_start_at_least_residue_and_follow_action": True,
        "periods_are_positive_minimal_return_times": True,
        "moduli": rows,
        "special_points": special_results,
        "distinct_tested_primitive_roots_across_orders": len(all_primitive),
        "distinct_tested_roots_including_1": len(largest_roots),
        "distinct_common_periodic_points_in_tested_projective_subset": (
            len(finite_projective_set)
        ),
        "infinitude_proved_here": False,
    }


def main():
    result = {
        "status": "PASS",
        "scope": "Exact finite checks only; no infinitude or unbounded iterate conclusion",
        "polynomials": check_polynomials(),
        "roots_and_projective_points": check_root_actions(),
    }
    result["explicit_runtime_check_count"] = CHECK_COUNT
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
