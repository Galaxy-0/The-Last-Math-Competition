import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Analysis.Real.Cardinality
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Data.Set.Countable

namespace TLMC3480

/-- Every finite simple graph, allowing arbitrary finite vertex count. -/
abbrev FiniteGraph := Σ n : ℕ, SimpleGraph (Fin n)

theorem countable_finite_graphs : Countable FiniteGraph := inferInstance

theorem uncountable_unit_interval : ¬ (Set.Icc (0 : ℝ) 1).Countable := by
  intro hc
  let j : ℝ → ℝ := fun x => (Real.arctan x + Real.pi / 2) / Real.pi
  have hj : Function.Injective j := by
    intro x y h
    have h' : Real.arctan x + Real.pi / 2 =
        Real.arctan y + Real.pi / 2 := by
      apply (div_left_inj' (ne_of_gt Real.pi_pos)).mp
      exact h
    exact Real.arctan_injective (add_right_cancel h')
  have hr : (Set.range j).Countable := hc.mono (by
    rintro y ⟨x, rfl⟩
    constructor
    · apply div_nonneg
      · linarith [Real.neg_pi_div_two_lt_arctan x]
      · exact le_of_lt Real.pi_pos
    · apply (div_le_iff₀ Real.pi_pos).2
      linarith [Real.arctan_lt_pi_div_two x])
  have hu : (Set.univ : Set ℝ).Countable := by
    have hp := hr.preimage hj
    simpa only [Set.preimage_range, Set.univ_inter] using hp
  exact Set.not_countable_univ hu

/-- No pair of real-valued invariants of finite simple graphs can have their
difference take every value in the real interval from zero to one. -/
theorem no_full_interval_of_difference
    (fractionalChromatic fractionalHall : FiniteGraph → ℝ) :
    ¬ Set.Icc (0 : ℝ) 1 ⊆
      Set.range (fun G : FiniteGraph => fractionalChromatic G - fractionalHall G) := by
  intro h
  have hr : (Set.range (fun G : FiniteGraph =>
      fractionalChromatic G - fractionalHall G)).Countable :=
    Set.countable_range _
  exact uncountable_unit_interval (hr.mono h)

#print axioms no_full_interval_of_difference

end TLMC3480
