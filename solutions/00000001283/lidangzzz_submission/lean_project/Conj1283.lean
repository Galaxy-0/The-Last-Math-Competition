/-
  TLMC #1283 DISPROOF (standalone)
-/

import Mathlib

namespace TLMC1283

/-! ## #1283 — the nim-equation x ⊕ y = x·y -/

/-- Conjecture #1283: the only solutions (in x, y ≥ 1) are (2,2) and (0,0). -/
def conjecture1283 : Prop :=
  ∀ x y : ℕ, 1 ≤ x → 1 ≤ y →
    (x ^^^ y = x * y ↔ ((x = 2 ∧ y = 2) ∨ (x = 0 ∧ y = 0)))

theorem conjecture1283_false : ¬ conjecture1283 := by
  intro h
  have h2 := h 2 2 (by norm_num) (by norm_num)
  have hne : ¬(2 ^^^ 2 = 2 * 2) := by decide
  exact hne (h2.mpr (Or.inl ⟨rfl, rfl⟩))


end TLMC1283
