# Disproof of conjecture 00000003713

The actual filled 2-simplex has first cohomology zero, but the degree-one
upper Laplacian has nonzero kernel. The cochain (1,1,0) is an actual
nonzero coboundary killed by the upper term. The full Hodge Laplacian
contains an additional lower term; the source specifically says upper.

Complete report: proof.tex and compiled proof.pdf. Lean project: lean/,
Lean 4.19.0, Mathlib c44e0c8ee63ca166450922a373c7409c5d26b00b.
Reproduce: cd lean; lake update; lake build. Report: tectonic proof.tex.

Validation: one successful final full lake build after draft finite-face,
quotient membership and matrix simp fixes. Seven audits contain only
propext/Classical.choice/Quot.sound. The single-page PDF was compiled,
rendered and visually inspected. The formalization constructs actual
faces, oriented incidence, cohomology quotient and transpose-product
upper operator; it does not stipulate cohomology or a kernel matrix.
Ignored local dependency junctions and build outputs are not submitted.
