# Build and axiom audit

- Lean: `leanprover/lean4:v4.33.1`.
- Mathlib revision: `0df444a360eaa60ab8c11dca51a86af692955474`.
- `lake build`: succeeded for the current `Main.lean` (2499 jobs).
- `#print axioms TLMC7766.no_claimed_value_set`: `propext`, `Classical.choice`, `Quot.sound` only.
- No `sorry`, `admit`, `native_decide`, or custom axiom is used.
- No auxiliary computation is required.
