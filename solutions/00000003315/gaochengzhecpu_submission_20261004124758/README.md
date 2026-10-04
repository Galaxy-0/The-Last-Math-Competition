# Conjecture 00000003315: quadratic circuit generation is false

Let P be the triangle with vertices (0,0), (2,1), and (1,2). Its full set of lattice points is (1,1), (2,1), (1,2), (0,0). The homogenized toric map over the rationals sends the corresponding variables to txy, tx²y, txy², t. Its kernel contains the nonzero cubic X1 X2 X3 - X0³, whereas every kernel binomial of degree at most two is zero. Consequently no set of quadratic circuit relations can generate this toric ideal.

## Files

- `main.tex`, `main.pdf`: self-contained disproof and formalization correspondence.
- `SOURCE.md`: exact original bilingual source bytes.
- `lean/Main.lean`: actual polynomial rings, algebra homomorphism, kernel ideal, ideal spans, and the full lattice-point proof.
- `lean/lean-toolchain`, `lean/lakefile.toml`, `lean/lake-manifest.json`: portable pinned Lean project.
- `verify.py`: supplementary exact integer and rational calculations using Python's standard library.
- `verification/BUILD.json` and logs: actual validation evidence.
- `verification/SELF_REVIEW.md`: authoring-agent adversarial review.

## Reproduction

Inside `lean/`, run:

```text
lake build
lake env lean -DwarningAsError=true Main.lean
```

The toolchain is Lean 4.19.0; Mathlib is pinned to public commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`. All transitive dependencies are pinned in the manifest. The portable project configuration contains no local dependency paths. On a new machine, `lake exe cache get` can fetch the official Mathlib cache.

From the submission directory, run:

```text
python verify.py
tectonic main.tex
```

## What Lean proves

`InTriangle` is the ordinary closed-triangle membership condition expressed through real nonnegative barycentric weights summing to one. `triangle_lattice_points` proves the complete list for arbitrary integer coordinates. `configuration_is_exact_triangle` connects that list directly to the columns used by the algebra map.

`Source` and `Target` are genuine `MvPolynomial` rings over the rationals. `toricMap` is an actual algebra homomorphism, and `toricIdeal` is its `RingHom.ker`. The homogenizing coordinate is included: the point (0,0) gives the monomial t, not 1.

For arbitrary exponent vectors and rational coefficients, `toricMap_monomial` proves the actual substitution formula. `degreeOfExponent_eq_sum` identifies the four-coordinate total with the finitely supported exponent sum. `low_degree_image_injective` proves injectivity when both exponent sums are at most two, using exact linear integer arithmetic. The first target coordinate preserves the degree, so the proof needs only one of the two stated bounds.

`LowDegreeBinomial` allows arbitrary rational coefficients and any two monomial exponents of degree at most two, including constants and linear terms. `low_degree_binomial_in_kernel_eq_zero` proves every such kernel element vanishes. `cubic_as_expression`, `cubic_in_kernel`, and `cubic_nonzero` verify the exhibited polynomial as an actual nonzero element of the kernel.

`no_quadratic_binomial_generating_set` rules out every set S consisting of these polynomials with `Ideal.span S = toricIdeal`. Membership of the generators in the kernel follows from this proposed span equality; it is not assumed without justification. All quadratic circuit relations are included among the binomials excluded by this stronger result.

The delivered conclusion concerns quadratic binomial generation. It does not claim a separate formal classification of arbitrary quadratic polynomials, circuit minimality of the cubic, the entire kernel, or Markov bases. Those results are not needed to disprove the source's universal generation assertion.

## Verification and review

`BUILD.json` records the actual fresh build and direct Lean commands, exit codes, audited theorem axioms, source hashes, and PDF checks. Fresh validation reuses only the unmodified pinned dependency cache, never this submission's compiled artifacts. No proof gaps, custom axioms, opaque declarations, or native computation shortcuts are used.

The Python supplement enumerates all fifteen exponent vectors of total degree at most two, proves their images distinct by exact comparison, checks the integer points against rational barycentric coordinates, and verifies both sides of the cubic map to exponent (3,3,3). The universal ideal assertion and the completeness of the geometric lattice-point list are proved in Lean, independently of the Python enumeration.

The built-in LaTeX editor and compiler are requested, with their actual outcome recorded. The deliverable PDF is produced by the existing Tectonic installation and every page is visually reviewed. Parent review and fresh upstream source/duplicate checks are separate before publication. The authoring agent makes no GitHub writes.
