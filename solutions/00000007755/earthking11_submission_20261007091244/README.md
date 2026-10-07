# Disproof of conjecture 00000007755 (first assertion)

The conjecture says that for each fixed degree there are only finitely many postcritically finite polynomials with algebraic coefficients. As stated, this is false already in degree 2. For every algebraic number `a`, the polynomial

`f_a(X) = (X-a)^2+a`

has unique critical point `a`, and `f_a(a)=a`. Its distinct parameters give distinct polynomials. Thus there are infinitely many quadratic PCF polynomials over the algebraic closure of `Q`.

The Lean theorem `TLMC7755.infinite_quadratic_pcf` formalizes this assertion for `Polynomial (AlgebraicClosure ℚ)`. The definition of PCF quantifies over **all** critical points in that algebraic closure, using the derivative and eventual repetition of the evaluation orbit. The theorem proves the actual set of degree-2 PCF polynomials infinite. The accompanying LaTeX report explains the mathematics and the scope.

This refutes the conjecture's literal first assertion, so no conclusion about the separately mentioned height asymptotic is needed. The statement does not quotient polynomials by affine conjugacy or restrict them to a normalized family; all the examples here are affine conjugate, so this argument does not address a conjecture with such an added restriction.

## Reproduce

From `lean/`, run `lake build`. The project locks Lean and Mathlib in `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json`. `#print axioms infinite_quadratic_pcf` is included at the end of `Main.lean`.
