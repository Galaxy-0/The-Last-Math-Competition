# Disproof of conjecture 00000002760

The full 1x1 rational matrix space is k-Engel for every positive k.
Its actual dimension, and the maximum dimension of such subspaces, is 1.
The proposed n^2 - n + c(k) formula forces c(k) = 1 for all positive k,
which contradicts convergence to zero. The source does not exclude n = 1.

Complete report: proof.tex and compiled proof.pdf. Lean project: lean/,
Lean 4.19.0 with Mathlib c44e0c8ee63ca166450922a373c7409c5d26b00b.
Reproduce: cd lean; lake update; lake build. Report: tectonic proof.tex.

Validation: one successful full final lake build after fixing two draft
finrank simplifications. Seven final audits contain only propext,
Classical.choice and Quot.sound. The PDF compiled, its single page was
rendered and visually inspected; the author line was additionally checked
at original resolution. Local junctions and build products are ignored.
