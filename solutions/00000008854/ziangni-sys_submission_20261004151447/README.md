# Disproof of conjecture 00000008854

Standard metric projected gradient on the real Hilbert space uses the identity metric and the full constraint set, with objective f(x)=2x². The metric spectrum is {1}, so its spectral midpoint is 1. The actual gradient is 4x; that step has orbit (-3)^n from 1 and diverges, whereas step 1/4 terminates at the unique minimizer after one update and uniquely minimizes the actual global error factor.

This targets the source's explicit metric-matrix midpoint claim under the standard metric projected-gradient definition. It distinguishes the metric from the objective Hessian. Complete report.tex/report.pdf and actual Mathlib derivative/gradient, projection minimization, matrix/CLM eigenvalue, iterate and limit proofs are included.

From lean/, run `lake build` with Lean4.19.0 and the public pinned Mathlib c44e0c8ee63ca166450922a373c7409c5d26b00b. Local build junctions are ignored; all submitted dependency pins are public.
