# Disproof of conjecture 00000001645

The rational group-ring matrix [1/2 e] for the trivial group has genuine Fuglede–Kadison determinant 1/2, which is not an algebraic integer or algebraic unit. The trivial group is torsion-free and satisfies the strong Atiyah condition because von Neumann dimensions are ordinary finite complex kernel dimensions.

The certificate constructs the monoid algebra, convolution regular action, singleton regular matrix, canonical trace and one-dimensional spectral logarithm. It computes exp(trace(log |T|)) and proves nonintegrality over Z. The report explains the finite-dimensional dimension bridge and distinguishes the explicit rational-matrix assertion from the usual integral-group-ring lower-bound conjecture.

## Reproduce

Use Lean 4.19.0 and run `lake build` in `lean/`. Mathlib is pinned publicly to c44e0c8ee63ca166450922a373c7409c5d26b00b. Local cache junctions are ignored and are not part of the submission.

`proof.tex` was compiled with Tectonic; `proof.pdf` was rendered with Poppler and visually checked. The full Lean build succeeded, with final theorem audits using only propext, Classical.choice and Quot.sound (some theorems require fewer).

Reference for the defining formula: Pierre de la Harpe, https://arxiv.org/abs/1107.1059, Section 3, formula (6).
