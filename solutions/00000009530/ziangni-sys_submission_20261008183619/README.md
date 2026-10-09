# Counterexample to 00000009530

Qubit dephasing fixes the distinct full-rank density matrices diag(9/25,16/25) and diag(16/25,9/25). Their actual Petz divergence at alpha = 1/2 is -2 log(24/25) > 0, so exact data-processing equality holds. The channel kills a nonzero off-diagonal matrix and is therefore not unitary on the full reference support. Its full-rank reference output also rules out any one-dimensional collapse.

This targets the pairwise equality definition in the source. It does not assert that dephasing is a global divergence isometry for every input pair.

The complete proof appears in `report.pdf` and `report.tex`. Lean checks complete positivity at every finite ancillary dimension, actual canonical square roots and divergence, and both excluded channel classes. Run `lake build` inside `lean/` using Lean 4.19.0 and the pinned public Mathlib dependencies.
