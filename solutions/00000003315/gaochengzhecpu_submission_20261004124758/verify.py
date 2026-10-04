"""Exact supplementary checks for the lattice configuration in conjecture 3315."""
from fractions import Fraction
from itertools import product
import json


def main():
    points = ((1, 1), (2, 1), (1, 2), (0, 0))
    columns = tuple((1, x, y) for x, y in points)

    # Every triangle point has x,y >= 0 and x+y <= 3, so this box
    # includes all possible lattice points. Membership itself is exact.
    lattice_points = []
    barycentric = {}
    for x, y in product(range(4), repeat=2):
        b = Fraction(2 * x - y, 3)
        c = Fraction(2 * y - x, 3)
        a = 1 - b - c
        if min(a, b, c) >= 0:
            assert a + b + c == 1
            assert 2 * b + c == x and b + 2 * c == y
            lattice_points.append((x, y))
            barycentric[f"({x},{y})"] = [str(a), str(b), str(c)]
    assert set(lattice_points) == set(points)

    def image(e):
        return tuple(sum(e[i] * columns[i][j] for i in range(4)) for j in range(3))

    low_exponents = [e for e in product(range(3), repeat=4) if sum(e) <= 2]
    assert len(low_exponents) == 15
    images = [image(e) for e in low_exponents]
    assert len(set(images)) == 15
    assert all(image(e)[0] == sum(e) for e in low_exponents)

    positive = (0, 1, 1, 1)
    negative = (3, 0, 0, 0)
    assert positive != negative
    assert sum(positive) == sum(negative) == 3
    assert image(positive) == image(negative) == (3, 3, 3)

    # The unique integral direction used in the written proof is checked
    # algebraically. The universal kernel calculation is proved in Lean.
    direction = (-3, 1, 1, 1)
    assert image(direction) == (0, 0, 0)

    print(json.dumps({
        "status": "PASS",
        "arithmetic": "exact integers and fractions; no floating-point sampling",
        "lattice_points": lattice_points,
        "barycentric_coordinates": barycentric,
        "homogenized_columns": columns,
        "degree_at_most_two_count": len(low_exponents),
        "distinct_image_count": len(set(images)),
        "monomial_image_table": [
            {"source": e, "target": image(e)} for e in low_exponents
        ],
        "cubic_positive_exponent": positive,
        "cubic_negative_exponent": negative,
        "common_cubic_image": image(positive),
        "scope": "Supplementary witness check; Lean proves geometry completeness and the universal ideal-span obstruction.",
    }, indent=2))


if __name__ == "__main__":
    main()
