import Conjecture3794.Problem
import Mathlib.Data.Set.Card

/-! The actual solution set is infinite, so no finite universal solution-count bound holds. -/
noncomputable section

namespace Conjecture3794

/-- Count every real solution, allowing an infinite solution set. -/
def SolutionCountBound : Prop :=
  ∀ n : ℕ, 0 < n → ∀ (M : Matrix (Fin n) (Fin n) ℝ) (q : Fin n → ℝ),
    (LCPSolutions M q).encard ≤ (2 : ℕ∞) ^ n

def solutionSequence (k : ℕ) : Fin 2 → ℝ := diagonalVector (k : ℝ)

theorem solutionSequence_mem (k : ℕ) :
    solutionSequence k ∈ LCPSolutions counterMatrix 0 :=
  diagonalVector_mem _ (by positivity)

theorem solutionSequence_injective : Function.Injective solutionSequence := by
  intro a b h
  have hreal : (a : ℝ) = (b : ℝ) := diagonalVector_injective h
  exact_mod_cast hreal

theorem counterSolutions_infinite : (LCPSolutions counterMatrix 0).Infinite :=
  Set.infinite_of_injective_forall_mem solutionSequence_injective solutionSequence_mem

/-- Extended natural cardinality records the proven infinitude as infinity. -/
theorem counterSolutions_encard : (LCPSolutions counterMatrix 0).encard = ⊤ :=
  Set.encard_eq_top counterSolutions_infinite

theorem counterSolutions_exceed_every_finite_bound (k : ℕ) :
    (k : ℕ∞) < (LCPSolutions counterMatrix 0).encard := by
  rw [counterSolutions_encard]
  simp

/-- Five distinct concrete solutions already exceed the claimed order-two bound of four. -/
theorem five_distinct_solutions :
    ∃ f : Fin 5 → {x // x ∈ LCPSolutions counterMatrix 0}, Function.Injective f := by
  refine ⟨fun k => ⟨solutionSequence k.val, solutionSequence_mem k.val⟩, ?_⟩
  intro a b h
  apply Fin.ext
  exact solutionSequence_injective (congrArg Subtype.val h)

theorem counterSolutions_not_le_two_pow_two :
    ¬ (LCPSolutions counterMatrix 0).encard ≤ (2 : ℕ∞) ^ 2 := by
  rw [counterSolutions_encard]
  norm_num

/-- A nonzero positive semidefinite matrix has an infinite LCP solution set. -/
theorem conjecture3794_counterexample :
    counterMatrix ≠ 0 ∧ counterMatrix.PosSemidef ∧
      (LCPSolutions counterMatrix 0).Infinite ∧
      ¬ (LCPSolutions counterMatrix 0).encard ≤ (2 : ℕ∞) ^ 2 :=
  ⟨counterMatrix_ne_zero, counterMatrix_posSemidef, counterSolutions_infinite,
    counterSolutions_not_le_two_pow_two⟩

/-- Direct negation of the unrestricted solution-count assertion in the source. -/
theorem conjecture3794_disproof : ¬ SolutionCountBound := by
  intro h
  exact counterSolutions_not_le_two_pow_two (h 2 (by norm_num) counterMatrix 0)

end Conjecture3794
