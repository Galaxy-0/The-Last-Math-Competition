import Conjecture7790.Definitions
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Tactic

noncomputable section
open MeasureTheory ProbabilityTheory Real Set
namespace Conjecture7790

theorem density_eq_exponentialPDF (x : ℝ) :
    ENNReal.ofReal (density x) = exponentialPDF 1 (x + 1) := by
  rw [exponentialPDF_eq]
  by_cases h : -1 ≤ x
  · have h2 : 0 ≤ x + 1 := by linarith
    simp [density, h, h2]
  · have h2 : ¬0 ≤ x + 1 := by linarith
    simp [density, h, h2]

/-- The proposed density is proved to describe the actual pushed-forward law. -/
theorem centeredExponential_eq_withDensity :
    centeredExponential = volume.withDensity (fun x => ENNReal.ofReal (density x)) := by
  ext s hs
  have hm : Measurable (fun y : ℝ => y - 1) := measurable_id.sub_const 1
  rw [centeredExponential, Measure.map_apply hm hs]
  change (volume.withDensity (exponentialPDF 1)) ((fun y : ℝ => y - 1) ⁻¹' s) = _
  rw [withDensity_apply _ (hm hs), withDensity_apply _ hs,
    ← lintegral_indicator (hm hs), ← lintegral_indicator hs]
  rw [← lintegral_add_right_eq_self
    (((fun y : ℝ => y - 1) ⁻¹' s).indicator (exponentialPDF 1)) (1 : ℝ)]
  apply lintegral_congr
  intro x
  by_cases hx : x ∈ s
  · have hpre : x + 1 ∈ ((fun y : ℝ => y - 1) ⁻¹' s) := by simpa using hx
    rw [Set.indicator_of_mem hpre, Set.indicator_of_mem hx, density_eq_exponentialPDF]
  · have hpre : x + 1 ∉ ((fun y : ℝ => y - 1) ⁻¹' s) := by simpa using hx
    rw [Set.indicator_of_not_mem hpre, Set.indicator_of_not_mem hx]

end Conjecture7790
