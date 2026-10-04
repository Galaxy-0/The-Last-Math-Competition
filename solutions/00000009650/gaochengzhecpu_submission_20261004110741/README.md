# Conjecture 00000009650 — Disproof

With the source's same-matrix definition, distinct-eigenvalue cross-overlaps
of a real symmetric matrix are all zero. Thus the strict-upper empirical law
is a point mass at zero, the mean is zero, and the scaled mean cannot tend to 2.
This applies pointwise to the real symmetric case (including GOE).

## Reproduce

With Lean 4.19.0, from `lean/`:

```sh
lake update
lake exe cache get Mathlib/Analysis/InnerProductSpace/Spectrum.lean Mathlib/LinearAlgebra/Matrix/Hermitian.lean Mathlib/Tactic/NormNum.lean Mathlib/Tactic/Positivity.lean
lake build
lake env lean -DwarningAsError=true Main.lean
```

Mathlib is locked at `c44e0c8ee63ca166450922a373c7409c5d26b00b` (v4.19.0).
Transitive dependencies are locked in the portable public-Git manifest.

From the submission directory:

```sh
python verify.py
tectonic main.tex
```

## What is proved

Lean proves orthogonality from actual self-adjointness and distinct real
eigenvalues; the point-mass identity for every empirical test function; the
exact mean contradiction; and the scaled-limit contradiction for any sequence
of real symmetric simple-spectrum eigensystems. It also constructs concrete
diagonal operators at every dimension, with normalized genuine eigenvectors,
distinct eigenvalues, and the violated mean formula.

The manuscript supplies the elementary measure interpretation, the GOE
almost-sure simplicity observation, and an optional discussion of inclusive
diagonals. The Lean project is not represented as a construction of Gaussian
probability laws. Its pointwise theorem requires no probabilistic assumption,
sampling experiment or random-matrix universality result.

Python checks exact rational finite examples only. Actual fresh-project build
logs, direct Lean axiom output, source/PDF hashes and visual checks appear in
`verification/`. Official dependency artifacts are reused at their locked
versions; the submission itself is freshly built. `SELF_REVIEW.md` is a
separate adversarial self-review by the same assistant, not independent review.
AI-assisted submission by gaochengzhecpu.
