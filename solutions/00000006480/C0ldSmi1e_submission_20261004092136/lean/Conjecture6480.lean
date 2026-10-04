import Conjecture6480.Processes
import Conjecture6480.Gaussian

/-! Explicit witnesses for conjecture 00000006480. -/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Conjecture6480

theorem same_covariance : covarianceMatrix X = covarianceMatrix Y := by
  rw [covariance_X, covariance_Y]

theorem different_joint_laws : jointLaw X ≠ jointLaw Y := by
  intro h
  have he := congrArg (fun ν : Measure (Fin 3 → ℝ) => ν {allNegative}) h
  change jointLaw X {allNegative} = jointLaw Y {allNegative} at he
  rw [joint_negative_X, joint_negative_Y] at he
  norm_num at he

theorem different_extreme_laws : extremeLaw X ≠ extremeLaw Y := by
  intro h
  have he := congrArg (fun ν : Measure ℝ => ν {(-1 : ℝ)}) h
  change extremeLaw X {(-1 : ℝ)} = extremeLaw Y {(-1 : ℝ)} at he
  rw [extreme_negative_X, extreme_negative_Y] at he
  norm_num at he

theorem X_nonGaussian : ¬ GaussianProcess μ X :=
  not_gaussianProcess_of_coordinate_zero_half_atom μ X (-1) coordinate0_atom_X

theorem Y_nonGaussian : ¬ GaussianProcess μ Y :=
  not_gaussianProcess_of_coordinate_zero_half_atom μ Y (-1) coordinate0_atom_Y

/-- The statistic used for the extremal law is an upper bound on every coordinate. -/
theorem coordinate_le_peak (Z : Fin 3 → Ω → ℝ) (ω : Ω) (i : Fin 3) :
    Z i ω ≤ peak Z ω := by
  fin_cases i
  · exact le_max_left _ _
  · exact (le_max_left _ _).trans (le_max_right _ _)
  · exact (le_max_right _ _).trans (le_max_right _ _)

/-- The statistic is attained by a coordinate, so it is exactly the finite-process maximum. -/
theorem peak_attained (Z : Fin 3 → Ω → ℝ) (ω : Ω) :
    ∃ i : Fin 3, peak Z ω = Z i ω := by
  rcases le_total (Z 0 ω) (max (Z 1 ω) (Z 2 ω)) with h | h
  · rw [peak, max_eq_right h]
    rcases le_total (Z 1 ω) (Z 2 ω) with h' | h'
    · exact ⟨2, max_eq_right h'⟩
    · exact ⟨1, max_eq_left h'⟩
  · exact ⟨0, max_eq_left h⟩

/-- A concrete finite probability-space witness for the source's existential claim.
The probability space and index set are fixed explicitly; this is sufficient for
existence, and does not assert a restriction on all processes in the source. -/
def ExplicitWitnessClaim : Prop :=
  IsProbabilityMeasure μ ∧
    ∃ P Q : Fin 3 → Ω → ℝ,
      (∀ i, Measurable (P i) ∧ Measurable (Q i)) ∧
      (∀ i, Integrable (P i) μ ∧ Integrable (Q i) μ) ∧
      (∀ i j,
        Integrable (fun ω => (P i ω - mean P i) * (P j ω - mean P j)) μ ∧
        Integrable (fun ω => (Q i ω - mean Q i) * (Q j ω - mean Q j)) μ) ∧
      ¬ GaussianProcess μ P ∧ ¬ GaussianProcess μ Q ∧
      covarianceMatrix P = covarianceMatrix Q ∧
      jointLaw P ≠ jointLaw Q ∧ extremeLaw P ≠ extremeLaw Q

theorem conjecture_true : ExplicitWitnessClaim := by
  refine ⟨inferInstance, X, Y, ?_, ?_, ?_, X_nonGaussian, Y_nonGaussian,
    same_covariance, different_joint_laws, different_extreme_laws⟩
  · intro i
    exact ⟨coordinates_measurable X i, coordinates_measurable Y i⟩
  · intro i
    exact ⟨coordinates_integrable X i, coordinates_integrable Y i⟩
  · intro i j
    exact ⟨covariance_integrable X i j, covariance_integrable Y i j⟩

end Conjecture6480
