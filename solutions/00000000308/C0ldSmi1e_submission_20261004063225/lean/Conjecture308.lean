import ComplexBound

namespace Conjecture308

/-- The selected line is exactly the real axis, not a degenerate point. -/
theorem realAxis_eq_range : realAxis = Set.range (fun t : ℝ ↦ (t : ℂ)) := by
  ext z
  simp only [realAxis, realLine, Set.mem_setOf_eq, zero_add, mul_one, Set.mem_range]
  exact ⟨fun ⟨t, ht⟩ ↦ ⟨t, ht.symm⟩, fun ⟨t, ht⟩ ↦ ⟨t, ht.symm⟩⟩

theorem sqrt_two_mem_realAxis : (Real.sqrt 2 : ℂ) ∈ realAxis := by
  exact ⟨Real.sqrt 2, by simp⟩

/-- An explicit point lies both on the real axis and in the actual badly approximable set. -/
theorem bad_inter_realAxis_nonempty : (BadC ∩ realAxis).Nonempty := by
  exact ⟨(Real.sqrt 2 : ℂ), sqrt_two_mem_BadC, sqrt_two_mem_realAxis⟩

/-- The first conjunct of conjecture 00000000308, with nondegenerate real affine lines. -/
def lineEmptinessClaim : Prop :=
  ∀ a v : ℂ, v ≠ 0 → BadC ∩ realLine a v = ∅

/-- A nondegenerate real line with nonempty intersection disproves the universal claim. -/
theorem conjecture308_disproof : ¬ lineEmptinessClaim := by
  intro h
  have he := h 0 1 one_ne_zero
  have hn := bad_inter_realAxis_nonempty
  change (BadC ∩ realLine 0 1).Nonempty at hn
  rw [he] at hn
  exact Set.not_nonempty_empty hn

end Conjecture308
