# Disproof of conjecture 00000008790

The final universal negative-correlation feasibility claim fails for the down-closed family of sets of size at most one on two items. The feasible fractional point is (1/2,1/2); the actual finite probability measure has masses 1/8,3/8,3/8,1/8 on 00,01,10,11. Both selected and complement pairs are negatively correlated and marginals are preserved, but the infeasible output 11 has probability 1/8. This concerns sufficiency of pairwise correlation, not failure of a particular pipage algorithm.

The full argument is in report.tex and report.pdf. From lean/, run `lake build` with Lean 4.19.0; public Mathlib revision is pinned to c44e0c8ee63ca166450922a373c7409c5d26b00b. Local development junctions and build products are ignored. No extra computational source is needed.
