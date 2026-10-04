import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.NormedSpace.OperatorNorm.NormedSpace
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.NormNum

namespace NumericalRadiusCounterexample

noncomputable def unitNumericalValues (A : ℂ →L[ℂ] ℂ) : Set ℝ :=
  {r | ∃ v : ℂ, ‖v‖ = 1 ∧ r = ‖@inner ℂ ℂ _ v (A v)‖}

noncomputable def numericalRadius (A : ℂ →L[ℂ] ℂ) : ℝ :=
  sSup (unitNumericalValues A)

noncomputable def identity : ℂ →L[ℂ] ℂ :=
  ContinuousLinearMap.id ℂ ℂ

theorem identity_operator_norm : ‖identity‖ = 1 :=
  ContinuousLinearMap.norm_id

theorem identity_unit_value (v : ℂ) (hv : ‖v‖ = 1) :
    ‖@inner ℂ ℂ _ v (identity v)‖ = 1 := by
  simp only [identity, ContinuousLinearMap.id_apply]
  rw [inner_self_eq_norm_sq_to_K, hv]
  norm_num

theorem identity_numerical_values : unitNumericalValues identity = {1} := by
  ext r
  constructor
  · rintro ⟨v, hv, hr⟩
    rw [identity_unit_value v hv] at hr
    exact Set.mem_singleton_iff.mpr hr
  · intro hr
    have hr1 : r = 1 := Set.mem_singleton_iff.mp hr
    refine ⟨1, ?_, ?_⟩
    · norm_num
    · rw [hr1]
      symm
      exact identity_unit_value 1 (by norm_num)

theorem identity_numerical_radius : numericalRadius identity = 1 := by
  rw [numericalRadius, identity_numerical_values, csSup_singleton]

theorem identity_ratio : numericalRadius identity / ‖identity‖ = 1 := by
  rw [identity_numerical_radius, identity_operator_norm]
  norm_num

def ClaimedHalfUpperBound : Prop :=
  ∀ A : ℂ →L[ℂ] ℂ, 0 < ‖A‖ →
    numericalRadius A / ‖A‖ ≤ (1 : ℝ) / 2

theorem conjecture_7167_false : ¬ ClaimedHalfUpperBound := by
  intro h
  have hnorm : 0 < ‖identity‖ := by rw [identity_operator_norm]; norm_num
  have hb := h identity hnorm
  rw [identity_ratio] at hb
  norm_num at hb

end NumericalRadiusCounterexample

#print axioms NumericalRadiusCounterexample.identity_operator_norm
#print axioms NumericalRadiusCounterexample.identity_numerical_values
#print axioms NumericalRadiusCounterexample.identity_numerical_radius
#print axioms NumericalRadiusCounterexample.conjecture_7167_false
