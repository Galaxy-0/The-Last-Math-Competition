"""Independent exact rational checks for the actual 2-by-2 matrix witness."""
from fractions import Fraction as F
import json


def multiply(a, b):
    return [[sum(a[i][k] * b[k][j] for k in range(2)) for j in range(2)]
            for i in range(2)]


def transpose(a):
    return [list(row) for row in zip(*a)]


def scale(a, scalar):
    return [[scalar * value for value in row] for row in a]


def charpoly(a):
    """Coefficients in increasing powers: det(A), -tr(A), 1."""
    return [a[0][0] * a[1][1] - a[0][1] * a[1][0],
            -a[0][0] - a[1][1], F(1)]


def factors(r, s):
    return [r * s, -r - s, F(1)]


def main():
    a = [[F(1), F(3, 2)], [F(0), F(1)]]
    identity = [[F(1), F(0)], [F(0), F(1)]]
    gram = multiply(transpose(a), a)
    assert gram == [[F(1), F(3, 2)], [F(3, 2), F(13, 4)]]
    assert charpoly(a) == factors(F(1), F(1))
    assert charpoly(gram) == factors(F(4), F(1, 4))

    # U=U0/sqrt(5), V=V0/sqrt(5). All normalized products are rational.
    u0 = [[F(2), F(-1)], [F(1), F(2)]]
    v0 = [[F(1), F(-2)], [F(2), F(1)]]
    diagonal = [[F(2), F(0)], [F(0), F(1, 2)]]
    assert multiply(u0, transpose(u0)) == scale(identity, F(5))
    assert multiply(transpose(u0), u0) == scale(identity, F(5))
    assert multiply(v0, transpose(v0)) == scale(identity, F(5))
    assert multiply(transpose(v0), v0) == scale(identity, F(5))
    assert scale(multiply(multiply(u0, diagonal), transpose(v0)), F(1, 5)) == a

    eigenvalues = [F(1), F(1)]
    singular_values = [F(2), F(1, 2)]
    assert singular_values[0] >= singular_values[1] >= 0
    assert [s * s for s in singular_values] == [F(4), F(1, 4)]
    assert abs(eigenvalues[0]) >= abs(eigenvalues[1])
    product = singular_values[0] * singular_values[1]
    geometric_mean = F(1)
    assert geometric_mean >= 0 and geometric_mean * geometric_mean == product
    bound = (geometric_mean + singular_values[1]) / 2
    assert bound == F(3, 4) < abs(eigenvalues[1]) == 1
    assert sum(singular_values) == F(5, 2)
    print(json.dumps({
        "status": "PASS",
        "arithmetic": "exact fractions only; no floating-point arithmetic",
        "matrix": a,
        "gram_matrix": gram,
        "characteristic_polynomial_coefficients_ascending": charpoly(a),
        "gram_characteristic_polynomial_coefficients_ascending": charpoly(gram),
        "normalized_svd_identity": "A = U0*S*transpose(V0)/5",
        "unitarity_checks": "both sides for U0/sqrt(5) and V0/sqrt(5)",
        "eigenvalues_with_multiplicity": eigenvalues,
        "ordered_singular_values": singular_values,
        "sum_of_singular_values": sum(singular_values),
        "n": 2,
        "claimed_upper_bound": bound,
        "actual_eigenvalue_modulus": abs(eigenvalues[1]),
    }, default=str, indent=2))


if __name__ == "__main__":
    main()
