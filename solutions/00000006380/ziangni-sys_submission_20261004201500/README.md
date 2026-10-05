# Proof of conjecture 00000006380

Two actual mixed Galerkin schemes share the Euclidean velocity space, inner-product bilinear forms and underlying weak equations. The pressure line is strictly enriched to the full plane, increasing its dimension from one to two, while both genuine inf-sup constants remain one.

The Lean source proves the actual supremum over all nonzero velocities and infimum over all nonzero pressures, strict enrichment, actual finite dimensions, bilinearity, coercivity and unique mixed solutions for every right-hand side.

Read report.pdf or its complete report.tex source. Reproduce the formal proof by running lake build inside lean/ using Lean 4.19.0. The public Mathlib dependency is pinned to c44e0c8ee63ca166450922a373c7409c5d26b00b.

The source specifies no particular PDE or finite-element shape; the construction uses finite-dimensional mixed Galerkin schemes.
