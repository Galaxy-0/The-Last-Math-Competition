"""Exact fraction and sparse-polynomial checks for the compression witness.

The determinant identity is expanded with eight independent indeterminates:
four entries of Q and four entries subsequently interpreted as their conjugates.
No finite numerical sampling is used to justify a universal statement.
"""
from fractions import Fraction as F
import json


def mm(a, b):
    return [[sum(a[i][k] * b[k][j] for k in range(len(b)))
             for j in range(len(b[0]))] for i in range(len(a))]


def tr(a):
    return [list(row) for row in zip(*a)]


def det2(a):
    return a[0][0] * a[1][1] - a[0][1] * a[1][0]


ZERO_MONOMIAL = (0,) * 8


def const(c):
    return {} if c == 0 else {ZERO_MONOMIAL: F(c)}


def var(i):
    exponent = [0] * 8
    exponent[i] = 1
    return {tuple(exponent): F(1)}


def add(a, b):
    out = dict(a)
    for exponent, coefficient in b.items():
        out[exponent] = out.get(exponent, F(0)) + coefficient
        if not out[exponent]:
            del out[exponent]
    return out


def scale(a, c):
    return {exponent: coefficient * c for exponent, coefficient in a.items()
            if coefficient * c}


def mul(a, b):
    out = {}
    for ex, cx in a.items():
        for ey, cy in b.items():
            exponent = tuple(x + y for x, y in zip(ex, ey))
            out[exponent] = out.get(exponent, F(0)) + cx * cy
    return {exponent: coefficient for exponent, coefficient in out.items()
            if coefficient}


def polynomial_mm(a, b):
    out = []
    for i in range(len(a)):
        row = []
        for j in range(len(b[0])):
            value = {}
            for k in range(len(b)):
                value = add(value, mul(a[i][k], b[k][j]))
            row.append(value)
        out.append(row)
    return out


def polynomial_det2(a):
    return add(mul(a[0][0], a[1][1]), scale(mul(a[0][1], a[1][0]), F(-1)))


def main():
    operator = [[F(0), F(0)], [F(0), F(1)]]
    midpoint = F(1, 2)
    shifted = [[midpoint, F(0)], [F(0), -midpoint]]
    q0 = [[F(1)], [F(1)]]
    normalization_squared = F(1, 2)
    frame_norm_squared = mm(tr(q0), q0)[0][0] * normalization_squared
    compressed_operator = mm(mm(tr(q0), operator), q0)[0][0] * normalization_squared
    compressed_shift = mm(mm(tr(q0), shifted), q0)[0][0] * normalization_squared
    assert frame_norm_squared == 1
    assert compressed_operator == midpoint
    assert compressed_shift == 0
    assert det2(shifted) == F(-1, 4) != 0

    # Q and Q* are formal matrices: their entries are independent variables.
    q = [[var(0), var(1)], [var(2), var(3)]]
    qstar = [[var(4), var(6)], [var(5), var(7)]]
    b = [[const(F(1, 2)), const(0)], [const(0), const(F(-1, 2))]]
    generic_compression = polynomial_mm(polynomial_mm(qstar, b), q)
    compression_determinant = polynomial_det2(generic_compression)
    product_of_determinants = mul(polynomial_det2(qstar), polynomial_det2(q))
    assert compression_determinant == scale(product_of_determinants, F(-1, 4))
    gram_determinant = polynomial_det2(polynomial_mm(qstar, q))
    assert gram_determinant == product_of_determinants
    assert compression_determinant == scale(gram_determinant, F(-1, 4))

    print(json.dumps({
        'status': 'PASS',
        'arithmetic': 'exact fractions and canonical sparse rational polynomials',
        'matrix_T': operator,
        'midpoint': midpoint,
        'one_column_frame': '(1,1)^T / sqrt(2)',
        'frame_norm_squared': frame_norm_squared,
        'compressed_T': compressed_operator,
        'compressed_midpoint_I_minus_T': compressed_shift,
        'shifted_determinant': det2(shifted),
        'universal_polynomial_identity': 'det(Q* B Q) = (-1/4) det(Q* Q)',
        'independent_indeterminates': 8,
        'expanded_nonzero_terms': len(compression_determinant),
        'isometry_implication': 'Q*Q=I makes the determinant exactly -1/4',
        'universal_rank_and_set_statement': 'proved in Lean; no numerical sampling used',
    }, default=str, indent=2))


if __name__ == '__main__':
    main()
