# Disproof of conjecture 00000008235

The universal strict-positive English-versus-first-price revenue claim fails for two independent private values both identically1. With zero reserve and a deterministic tie rule, first-price bids (1,1) and ascending English dropout thresholds (1,1) are equilibria, covering every unilateral nonnegative deviation. Both mechanisms earn actual expected revenue1.

The distribution is explicitly degenerate. This refutes strict positivity, not a nonnegative linkage theorem, and makes no separate claim about Myerson reserves or asymptotics. The report includes the actual ascending-clock stopping rule and its uniqueness, payments, all equilibrium cases and probability integrals.

From lean/, run `lake build` with Lean4.19.0 and public Mathlib c44e0c8ee63ca166450922a373c7409c5d26b00b, pinned in the project. Local development junctions/build products are ignored.
