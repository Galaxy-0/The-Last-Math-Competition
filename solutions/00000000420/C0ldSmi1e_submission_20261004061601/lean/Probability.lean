import DensityIntegral
import DensityBounds
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

namespace Conjecture420

open MeasureTheory Filter
open scoped Topology ENNReal NNReal

/-- The formula in the conjecture has total mass `8√2/(3π)`. -/
theorem candidateMeasure_univ :
    candidateMeasure Set.univ = ENNReal.ofReal (8 * Real.sqrt 2 / (3 * Real.pi)) := by
  rw [candidateMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal rho_integrableOn]
  · rw [rho_setIntegral]
  · exact (ae_restrict_mem measurableSet_Icc).mono fun _ hx => rho_nonneg hx

/-- Its total mass is strictly greater than the unit mass of a probability measure. -/
theorem candidateMeasure_mass_gt_one : (1 : ℝ≥0∞) < candidateMeasure Set.univ := by
  rw [candidateMeasure_univ, ← ENNReal.ofReal_one]
  exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg zero_le_one).mpr mass_gt_one

/-- The displayed density fails the defining normalization of a probability measure. -/
theorem candidateMeasure_not_probability : ¬ IsProbabilityMeasure candidateMeasure := by
  intro hp
  exact (ne_of_gt candidateMeasure_mass_gt_one) hp.measure_univ

/-- No probability measure can equal the measure specified by the conjecture. -/
theorem no_probabilityMeasure_with_density :
    ¬ ∃ μ : ProbabilityMeasure ℝ, (μ : Measure ℝ) = candidateMeasure := by
  rintro ⟨μ, hμ⟩
  apply candidateMeasure_not_probability
  rw [← hμ]
  infer_instance

/-- The proposed measure is finite, so it belongs to the space of finite measures. -/
instance candidateMeasure_isFiniteMeasure : IsFiniteMeasure candidateMeasure where
  measure_univ_lt_top := by rw [candidateMeasure_univ]; exact ENNReal.ofReal_lt_top

noncomputable def candidateFiniteMeasure : FiniteMeasure ℝ := ⟨candidateMeasure, inferInstance⟩

@[simp] theorem candidateFiniteMeasure_toMeasure :
    (candidateFiniteMeasure : Measure ℝ) = candidateMeasure := rfl

theorem candidateFiniteMeasure_mass_gt_one : 1 < candidateFiniteMeasure.mass := by
  rw [← ENNReal.coe_lt_coe, FiniteMeasure.ennreal_mass]
  exact candidateMeasure_mass_gt_one

/-- Weak convergence of probability measures cannot have this finite measure as its limit:
the constant bounded continuous test function one preserves total mass. -/
theorem no_probability_weak_limit {ι : Type*} (l : Filter ι) [NeBot l]
    (μ : ι → ProbabilityMeasure ℝ) :
    ¬ Tendsto (fun i ↦ (μ i).toFiniteMeasure) l (𝓝 candidateFiniteMeasure) := by
  intro h
  have hmass := h.mass
  simp only [ProbabilityMeasure.mass_toFiniteMeasure] at hmass
  have heq : (1 : ℝ≥0) = candidateFiniteMeasure.mass :=
    tendsto_nhds_unique tendsto_const_nhds hmass
  exact (ne_of_lt candidateFiniteMeasure_mass_gt_one) heq

/-- In particular, no sequence of probability measures converges weakly to the conjectured density. -/
theorem no_probability_sequence_weak_limit (μ : ℕ → ProbabilityMeasure ℝ) :
    ¬ Tendsto (fun n ↦ (μ n).toFiniteMeasure) atTop (𝓝 candidateFiniteMeasure) :=
  no_probability_weak_limit atTop μ

end Conjecture420
