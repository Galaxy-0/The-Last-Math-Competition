# Build and axiom audit

- Lean: `leanprover/lean4:v4.33.1`.
- Mathlib revision: `0df444a360eaa60ab8c11dca51a86af692955474`.
- The decisive Lean theorems are `infinite_normalized_pcf_parameters`, `infinite_normalized_quadratic_pcf`, and `normalized_affine_conjugate_iff`.
- `#print axioms` for all three reports only `propext`, `Classical.choice`, and `Quot.sound`.
- No `sorry`, `admit`, `native_decide`, or custom axiom is used.
- No auxiliary computation is required.
