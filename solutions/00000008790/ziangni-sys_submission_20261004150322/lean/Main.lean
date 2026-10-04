import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Fin
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

open MeasureTheory
open scoped ENNReal Classical
noncomputable section
namespace NegativeRounding

abbrev Ω := Fin 2 × Fin 2
instance : MeasurableSpace Ω := ⊤
instance : MeasurableSingletonClass Ω := ⟨fun _ => trivial⟩
def weight (ω : Ω) : ℝ := if ω.1 = ω.2 then 1/8 else 3/8
def law : PMF Ω := PMF.ofFintype (fun ω => ENNReal.ofReal (weight ω)) (by
  norm_num [weight, Fintype.sum_prod_type, Fin.sum_univ_two, ← ENNReal.ofReal_add])
def μ : Measure Ω := law.toMeasure
instance : IsProbabilityMeasure μ := inferInstanceAs (IsProbabilityMeasure law.toMeasure)
def bit (ω : Ω) (i : Fin 2) : ℝ := if (if i = 0 then ω.1 else ω.2) = 1 then 1 else 0
def selected (ω : Ω) : Finset (Fin 2) := Finset.univ.filter (fun i => bit ω i = 1)
def family : Set (Finset (Fin 2)) := {s | s.card ≤ 1}
def feasibleFractional (x : Fin 2 → ℝ) : Prop :=
  (∀ i, 0 ≤ x i ∧ x i ≤ 1) ∧ ∑ i, x i ≤ 1
def fractional : Fin 2 → ℝ := fun _ => 1/2
def probability (s : Set Ω) : ℝ := (μ s).toReal

lemma univ_two : (Finset.univ : Finset (Fin 2)) = {0,1} := by
  ext i; fin_cases i <;> simp

lemma mass (s : Set Ω) : μ s =
    ∑ ω : Ω, if ω ∈ s then ENNReal.ofReal (weight ω) else 0 := by
  simp only [μ, law, PMF.toMeasure_ofFintype_apply _ _ (show MeasurableSet s from trivial),
    tsum_fintype]
  rfl

theorem zero_one (ω : Ω) (i : Fin 2) : bit ω i = 0 ∨ bit ω i = 1 := by
  by_cases h : (if i = 0 then ω.1 else ω.2) = 1 <;> simp [bit, h]

theorem expected_coordinate (i : Fin 2) : (∑ ω : Ω, weight ω * bit ω i) = fractional i := by
  fin_cases i <;> norm_num [weight, bit, fractional, Fintype.sum_prod_type, Fin.sum_univ_two]

lemma marginals (i : Fin 2) : probability {ω | bit ω i = 1} = 1/2 := by
  fin_cases i <;>
    norm_num [probability, mass, weight, bit, Fintype.sum_prod_type, Fin.sum_univ_two,
      ← ENNReal.ofReal_add]

lemma complements (i : Fin 2) : probability {ω | bit ω i = 0} = 1/2 := by
  fin_cases i <;>
    norm_num [probability, mass, weight, bit, Fintype.sum_prod_type, Fin.sum_univ_two,
      ← ENNReal.ofReal_add]

lemma joint_selected (i j : Fin 2) (h : i ≠ j) :
    probability {ω | bit ω i = 1 ∧ bit ω j = 1} = 1/8 := by
  fin_cases i <;> fin_cases j <;>
    norm_num [probability, mass, weight, bit, Fintype.sum_prod_type, Fin.sum_univ_two,
      ← ENNReal.ofReal_add] at *

lemma joint_unselected (i j : Fin 2) (h : i ≠ j) :
    probability {ω | bit ω i = 0 ∧ bit ω j = 0} = 1/8 := by
  fin_cases i <;> fin_cases j <;>
    norm_num [probability, mass, weight, bit, Fintype.sum_prod_type, Fin.sum_univ_two,
      ← ENNReal.ofReal_add] at *

def PairwiseNegative : Prop := ∀ i j : Fin 2, i ≠ j →
  probability {ω | bit ω i = 1 ∧ bit ω j = 1} ≤
    probability {ω | bit ω i = 1} * probability {ω | bit ω j = 1} ∧
  probability {ω | bit ω i = 0 ∧ bit ω j = 0} ≤
    probability {ω | bit ω i = 0} * probability {ω | bit ω j = 0}

theorem pairwise_negative : PairwiseNegative := by
  intro i j h
  rw [joint_selected i j h, joint_unselected i j h, marginals, marginals,
    complements, complements]
  norm_num

theorem down_closed : ∀ s ∈ family, ∀ t, t ⊆ s → t ∈ family := by
  intro s hs t ht
  exact le_trans (Finset.card_le_card ht) hs

theorem fractional_feasible : feasibleFractional fractional := by
  norm_num [feasibleFractional, fractional, Fin.sum_univ_two]

theorem infeasible_probability : probability {ω | selected ω ∉ family} = 1/8 := by
  norm_num [probability, mass, selected, family, weight, bit, Fintype.sum_prod_type,
    Fin.sum_univ_two, ← ENNReal.ofReal_add, univ_two, Finset.filter_insert, Finset.filter_singleton]

theorem positive_failure : 0 < probability {ω | selected ω ∉ family} := by
  rw [infeasible_probability]
  norm_num

theorem counterexample :
    (∀ s ∈ family, ∀ t, t ⊆ s → t ∈ family) ∧
    feasibleFractional fractional ∧
    (∀ i, probability {ω | bit ω i = 1} = fractional i) ∧
    PairwiseNegative ∧ 0 < probability {ω | selected ω ∉ family} :=
  ⟨down_closed, fractional_feasible, marginals, pairwise_negative, positive_failure⟩

#print axioms zero_one
#print axioms expected_coordinate
#print axioms marginals
#print axioms joint_selected
#print axioms joint_unselected
#print axioms pairwise_negative
#print axioms fractional_feasible
#print axioms infeasible_probability
#print axioms counterexample
end NegativeRounding
