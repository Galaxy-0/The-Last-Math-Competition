import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Analysis.Real.Cardinality
import Mathlib.Data.Set.Countable
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Algebra.AlgebraicCard

namespace TLMC7766

abbrev K := AlgebraicClosure ℚ
abbrev P1 := Option K

def Periodic (F : P1 → P1) (x : P1) : Prop :=
  ∃ n : ℕ, 0 < n ∧ (F^[n]) x = x

theorem countable_projective_line : Countable P1 := by
  letI : Algebra.IsAlgebraic ℚ K := AlgebraicClosure.isAlgebraic ℚ
  have hc : (Set.univ : Set K).Countable :=
    (Algebraic.countable ℚ K).mono (by
      intro x _
      exact Algebra.IsAlgebraic.isAlgebraic x)
  haveI : Countable K := Set.countable_univ_iff.mp hc
  infer_instance

instance : Countable P1 := countable_projective_line

theorem uncountable_upper_ray (c : ℝ) : ¬ (Set.Ici c).Countable := by
  intro hc
  let j : ℝ → ℝ := fun x => c + Real.exp x
  have hj : Function.Injective j := by
    intro x y h
    exact Real.exp_injective (add_left_cancel h)
  have hr : (Set.range j).Countable := hc.mono (by
    rintro y ⟨x, rfl⟩
    exact le_add_of_nonneg_right (le_of_lt (Real.exp_pos x)))
  have hu : (Set.univ : Set ℝ).Countable := by
    have hp := hr.preimage hj
    simpa only [Set.preimage_range, Set.univ_inter] using hp
  exact Set.not_countable_univ hu

theorem no_upper_ray_of_periodic_height_values
    (F : P1 → P1) (D : P1 → ℝ) (c : ℝ) :
    ¬ Set.Ici c ⊆ D '' {x : P1 | Periodic F x} := by
  intro h
  have hcnt : (D '' {x : P1 | Periodic F x}).Countable :=
    (Set.to_countable _).image D
  exact uncountable_upper_ray c (hcnt.mono h)

theorem no_claimed_value_set
    (F : P1 → P1) (D : P1 → ℝ) (c : ℝ) :
    D '' {x : P1 | Periodic F x} ≠ ({0} ∪ Set.Ici c) := by
  intro h
  apply no_upper_ray_of_periodic_height_values F D c
  rw [h]
  exact Set.subset_union_right

#print axioms no_claimed_value_set

end TLMC7766
