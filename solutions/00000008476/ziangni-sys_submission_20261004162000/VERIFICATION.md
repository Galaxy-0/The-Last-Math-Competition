# Verification

- Lean 4.19.0; Mathlib c44e0c8ee63ca166450922a373c7409c5d26b00b.
- Final full `lake build` passed 2173 targets with no warnings, after correcting development-build simplification errors.
- Nine printed theorem axiom audits use only `propext`, `Classical.choice`, and `Quot.sound`.
- No sorry, admit, native_decide, unsafe declarations, or custom axioms.
- Formal coverage: actual measurable partition atoms and their covering/disjointness, full iterated refinement, all partition-rate limits and entropy supremum, actual invariant ergodic probability measures and integrals, full pressure supremum, real analyticity, and distinct equilibrium states.
- Partition rates are defined using limsup; the ordinary normalized Shannon-entropy limit is proved zero, so this agrees with the usual Kolmogorov–Sinai rate. All partitions of the finite discrete space are finite and measurable and are included through their equivalence relations.
- The built-in LaTeX compiler encountered its known platform-directory failure. Existing Tectonic compiled the final PDF once. Both pages were rendered and inspected with no clipping or illegibility. PDF size: 35171 bytes.
