# Conjecture 00000002507: disproof

The genuine normalized Z-eigensystem of an order-three one-dimensional tensor with component 1 has valid pair (1,1), but doubling it to (2,2) violates the unit-vector condition. The common zero set of any family of ordinary homogeneous polynomials in the original affine variables is closed under scaling, so cannot define this Z-eigensystem.

## Formal scope

`Tensor` is the actual three-index array on Fin 1. The contraction is the finite double sum of tensor components times two vector components. `ZPair` includes that contracted eigen-equation and the sum-of-squared-coordinates normalization. Lean verifies the pair and its failed doubling. `homogeneous_scaling` proves the scalar covariance of arbitrary Mathlib `MvPolynomial.IsHomogeneous` polynomials via their monomial supports. The final theorem excludes every finite or infinite family of homogeneous polynomial equations in the actual eigenpair coordinates whose common zero set equals `ZPair`.

The obstruction is the normalized Z-eigensystem, specifically named in the English statement. The eigen-equation alone, projective homogenization with an additional chart variable, and unnormalized H-eigenvalue equations are different objects and do not remove the normalization obstruction in the original variables. No contraction or polynomial certificate is assumed.

## Reproduction

Use Lean 4.19.0 and Mathlib c44e0c8ee63ca166450922a373c7409c5d26b00b, publicly pinned in the lakefile and manifest. Run `cd lean`, `lake update` if packages are absent, then `lake build`. Ignored local `.lake` junctions are not submitted. Compile solution.tex with Tectonic or a standard LaTeX engine. No auxiliary computation is needed.

## Validation

One final successful full lake build compiled the complete project. All five final printed axiom audits reported exactly propext, Classical.choice, Quot.sound. The only linter warning is an unused index in a one-dimensional sum. No admissions, custom axioms, native decision or unsafe code occurs. The two-page PDF compiled with Tectonic without layout warnings, rendered with Poppler and both pages were visually inspected: no clipping, overlap or illegibility.
