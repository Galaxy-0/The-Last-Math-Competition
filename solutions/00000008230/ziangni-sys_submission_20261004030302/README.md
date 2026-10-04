# Disproof of Conjecture 00000008230

For the cyclic group C3 and the second Adams operation on complex class
functions, the fixed subspace has dimension 2. All three conjugacy classes
are 2-regular, so the conjectured dimension equality fails.

The Adams operation is `psi^k(f)(g) = f(g^k)`. In coordinates indexed by
the three elements `(1,a,a^2)`, `psi^2(u,v,w) = (u,w,v)`, so the fixed
space consists exactly of `(u,v,v)`. This is a two-dimensional complex
space, whereas every element has odd order and each conjugacy class is a
singleton.

The submission disproves the explicit fixed-space dimension conjunct in
both language versions of the original. It does not claim results about
the separate spectral-support or composition-correction assertions.

## Files

- `report.tex`, `report.pdf`: complete mathematical proof and correspondence.
- `lean/`: Lean 4.19.0 project, with pinned Mathlib dependencies.
- `VERIFICATION.md`: formal scope, checks, and final theorem axiom audit.

## Reproduction

From the `lean` directory, with the pinned Lean toolchain installed:

```sh
lake exe cache get
lake build
lake env lean Main.lean
```

Use a short checkout path on Windows if long Mathlib import paths exceed
the platform limit. Local dependency cache links and build products are
ignored and not included in the submission. The public manifest pins
upstream Git commits and contains no machine-specific paths.

For the PDF, run from this submission directory:

```sh
tectonic -X compile report.tex
```

The final theorem is `Adams8230.counterexample`. Its objects are the actual
cyclic group `Multiplicative (ZMod 3)`, its conjugacy-class quotient, its
element orders, and the complex submodule defined by class invariance and
the Adams fixed-point equation. The dimension is proved through an
explicit linear equivalence with `Complex × Complex`.
