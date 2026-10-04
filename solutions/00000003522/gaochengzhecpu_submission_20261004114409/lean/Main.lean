import Mathlib.SetTheory.Ordinal.NaturalOps

/-! Conjecture 3522: the genuine Hessenberg sum of arbitrary ordinals is
cancellative on both sides; ordinary ordinal addition is not right-cancellative.
The proof derives injectivity from the recursive order characterization,
rather than introducing an operation with cancellation as an assumption. -/

universe u

namespace Conjecture3522

open Ordinal
open scoped Ordinal NaturalOps

/-- Fixing the first summand of the genuine Hessenberg sum gives a strict
order-preserving function. This follows directly from its recursive lower set. -/
theorem natural_sum_strictMono_left (a : Ordinal.{u}) :
    StrictMono (fun b : Ordinal.{u} => a ♯ b) := by
  intro b c hbc
  exact Ordinal.lt_nadd_iff.mpr (Or.inr ⟨b, hbc, le_rfl⟩)

/-- The same strictness holds when the second summand is fixed. -/
theorem natural_sum_strictMono_right (a : Ordinal.{u}) :
    StrictMono (fun b : Ordinal.{u} => b ♯ a) := by
  intro b c hbc
  exact Ordinal.lt_nadd_iff.mpr (Or.inl ⟨b, hbc, le_rfl⟩)

theorem natural_sum_left_cancellation (a b c : Ordinal.{u}) :
    a ♯ b = a ♯ c ↔ b = c := by
  constructor
  · intro h
    exact (natural_sum_strictMono_left a).injective h
  · intro h
    rw [h]

theorem natural_sum_right_cancellation (a b c : Ordinal.{u}) :
    b ♯ a = c ♯ a ↔ b = c := by
  constructor
  · intro h
    exact (natural_sum_strictMono_right a).injective h
  · intro h
    rw [h]

/-- Ordinary addition has an explicit failure of right cancellation. -/
theorem ordinary_sum_witness :
    (0 : Ordinal.{u}) + ω = 1 + ω ∧ (0 : Ordinal.{u}) ≠ 1 := by
  constructor
  · rw [zero_add, Ordinal.one_add_omega0]
  · exact zero_ne_one

theorem ordinary_sum_not_right_cancellative :
    ¬ ∀ (a b c : Ordinal.{u}), b + a = c + a → b = c := by
  intro h
  exact ordinary_sum_witness.2 (h ω 0 1 ordinary_sum_witness.1)

/-- This direction is retained for ordinary addition: the counterexample
does not incorrectly claim that both ordinary cancellation directions fail. -/
theorem ordinary_sum_left_cancellation (a b c : Ordinal.{u}) :
    a + b = a + c ↔ b = c := add_left_cancel_iff

/-- The same two distinct ordinals remain distinguished by natural addition. -/
theorem natural_sum_distinguishes_witness :
    (0 : Ordinal.{u}) ♯ ω ≠ 1 ♯ ω := by
  intro h
  exact zero_ne_one ((natural_sum_right_cancellation ω 0 1).mp h)

/-- The complete assertion in the source, with both natural cancellation
directions and a concrete failure for ordinary ordinal addition. -/
theorem conjecture_true :
    (∀ (a b c : Ordinal.{u}), a ♯ b = a ♯ c ↔ b = c) ∧
    (∀ (a b c : Ordinal.{u}), b ♯ a = c ♯ a ↔ b = c) ∧
    (∃ (a b c : Ordinal.{u}), b ≠ c ∧ b + a = c + a) := by
  refine ⟨natural_sum_left_cancellation, natural_sum_right_cancellation, ?_⟩
  exact ⟨ω, 0, 1, ordinary_sum_witness.2, ordinary_sum_witness.1⟩

#print axioms natural_sum_strictMono_left
#print axioms natural_sum_strictMono_right
#print axioms natural_sum_left_cancellation
#print axioms natural_sum_right_cancellation
#print axioms ordinary_sum_witness
#print axioms ordinary_sum_not_right_cancellative
#print axioms ordinary_sum_left_cancellation
#print axioms natural_sum_distinguishes_witness
#print axioms conjecture_true

end Conjecture3522
