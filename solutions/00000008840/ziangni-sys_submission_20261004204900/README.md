# Disproof of conjecture 00000008840

An everywhere-defined real monotone step map takes values -1 on x≤0, zero on 0<x<1 and one on x≥1. Its actual zero set is (0,1), whose closure is [0,1]; hence the zero set is not closed. The actual Minty map x+A(x) also misses zero.

Lean verifies the full graph/domain, every-pair real Hilbert monotonicity, genuine zero set/topological closure, range obstruction and an explicit proper monotone extension by adjoining (0,0).

The source omits maximal monotonicity. The example disproves its unqualified closed-zero-set clause and preserves the correct theorem for maximal monotone operators.

Read report.pdf or report.tex; reproduce by running lake build inside lean/ with Lean 4.19.0 and the publicly pinned Mathlib dependency.
