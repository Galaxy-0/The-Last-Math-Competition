# Disproof of conjecture 00000001649

The predicted top degree for n=2 is floor(3/4)−1=−1. The actual group SL_2(Z) has nonzero ordinary rational degree-zero cohomology: H^0 ≅ Q, with the nonzero class of 1. Therefore its top nonzero degree cannot equal the proposed value.

The certificate uses Mathlib's determinant-one integer matrix group and a genuine cochain differential, cocycle kernel and boundary quotient. It certifies a nonzero class above the predicted top degree. No exact top-degree or higher-cohomology calculation is needed. Subtraction is integer subtraction, as in the mathematical formula, and n=2 is not excluded by the source.

## Reproduce

Run `lake build` in `lean/` with Lean 4.19.0. Public Mathlib is pinned to c44e0c8ee63ca166450922a373c7409c5d26b00b; ignored local cache junctions are not part of the submission.

The full build passed with standard-only final theorem axiom audits. The PDF was compiled with Tectonic, rendered with Poppler and visually checked.
