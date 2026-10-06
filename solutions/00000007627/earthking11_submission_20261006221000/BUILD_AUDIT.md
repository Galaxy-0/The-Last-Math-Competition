# Build and axiom audit

- Lean toolchain: `leanprover/lean4:v4.33.1`
- Mathlib revision: `0df444a360eaa60ab8c11dca51a86af692955474`
- Build command: `lake build`
- Build result: successful; `Main` compiled (3010 build jobs, about 4.9 seconds
  in the recorded run).
- The Lean source contains no `sorry`, `native_decide`, or custom axioms.
- `#print axioms` for `leftColumn0_minimal`, `leftColumn1_minimal`,
  `matrixOneFactorDecomposition`, `matrix_ring_center_finrank`,
  `minimal_left_ideal_count_ne_center_dimension`, and
  `minimal_left_ideal_count_ne_matrix_factor_count`, and the combined capstone
  `actual_matrix_counterexample` report only Lean's standard
  axioms `[propext, Classical.choice, Quot.sound]`.

The finite-field coordinate case split and finite cardinal argument are proved
in Lean. The central-dimension result uses Mathlib's `IsCentral` theorem for the
matrix algebra, not an asserted equality or a numeric surrogate.
