# Disproof of conjecture 00000005781

The canonical divergence on the Euclidean dually flat line with potential x²/2 is (x-y)²/2. Its additive triangle deficit at (0,1,2) is -1. The opposite sign convention also fails, at (0,2,1).

This refutes the original nonnegativity clause. Both source languages omit orthogonality and projection hypotheses that could control the sign.

## Formal model

Main.lean defines the actual real potential, proves its derivative and Hessian 1, proves strict convexity through a positive Jensen gap, and proves the Legendre maximum formula. The canonical divergence is constructed from primal and dual potentials and coordinates; it is proved equal to the Bregman formula. Its three-point remainder is computed from these definitions.

The final theorem is a necessary specialization of the asserted universal nonnegative-remainder claim. Constant-coordinate flatness of the geometric line is explained directly in the report; no general geometry theorem is represented as formalized.

## Reproduction

Lean 4.19.0 and pinned Mathlib:

    cd lean
    lake update
    lake exe cache get Mathlib/Analysis/Calculus/Deriv/Pow.lean Mathlib/Analysis/Calculus/Deriv/Mul.lean Mathlib/Analysis/Calculus/Deriv/Add.lean Mathlib/Tactic/Ring.lean Mathlib/Tactic/NormNum.lean Mathlib/Tactic/Linarith.lean
    lake build
    lake env lean Main.lean

Run Tectonic on report.tex to reproduce report.pdf.
See VERIFICATION.md for observed validation.
