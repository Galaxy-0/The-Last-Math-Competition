# Build and axiom audit

- Lean: `leanprover/lean4:v4.33.1`.
- Mathlib revision: `0df444a360eaa60ab8c11dca51a86af692955474`.
- `lake build`: succeeded for the current `Main.lean` (1969 jobs).
- `#print axioms TLMC7755.infinite_quadratic_pcf`: `propext`, `Classical.choice`, `Quot.sound` only.
- No `sorry`, `admit`, `native_decide`, or custom axiom is used.
- No auxiliary computation is required.
