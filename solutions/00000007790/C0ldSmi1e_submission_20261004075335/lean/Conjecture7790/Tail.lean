import Conjecture7790.Definitions
import Mathlib.Tactic

noncomputable section
open MeasureTheory ProbabilityTheory Real Set
namespace Conjecture7790

/-- Exact right-tail probability for the actual rate-one exponential measure. -/
theorem exponential_right_tail {u : ℝ} (hu : 0 ≤ u) :
    (expMeasure 1).real (Ioi u) = Real.exp (-u) := by
  letI : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasureExponential (by norm_num)
  have hcdf : (expMeasure 1).real (Iic u) = 1 - Real.exp (-u) := by
    rw [← cdf_eq_real]
    change exponentialCDFReal 1 u = _
    rw [exponentialCDFReal_eq (by norm_num), if_pos hu]
    simp
  rw [← compl_Iic, measureReal_compl measurableSet_Iic, hcdf]
  simp [measureReal_def]

/-- Exact right-tail probability of the centered law (strict endpoint is immaterial here). -/
theorem centered_right_tail {u : ℝ} (hu : -1 ≤ u) :
    centeredExponential.real (Ioi u) = Real.exp (-(u + 1)) := by
  have hm : Measurable (fun y : ℝ => y - 1) := measurable_id.sub_const 1
  rw [measureReal_def, centeredExponential, Measure.map_apply hm measurableSet_Ioi]
  have hpre : (fun y : ℝ => y - 1) ⁻¹' Ioi u = Ioi (u + 1) := by
    ext y
    simp only [mem_preimage, mem_Ioi]
    constructor <;> intro h <;> linarith
  rw [hpre]
  exact exponential_right_tail (by linarith)

/-- The positive excursion is contained in the absolute-value tail. -/
theorem norm_tail_lower_bound {u : ℝ} (hu : 0 ≤ u) :
    Real.exp (-(u + 1)) ≤ centeredExponential.real {x : ℝ | u ≤ |x|} := by
  letI : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasureExponential (by norm_num)
  letI : IsProbabilityMeasure centeredExponential := by
    unfold centeredExponential
    exact isProbabilityMeasure_map (measurable_id.sub_const 1).aemeasurable
  rw [← centered_right_tail (by linarith : -1 ≤ u)]
  exact measureReal_mono (fun x hx => (le_of_lt hx).trans (le_abs_self x))

/-- No positive Gaussian-decay constant can bound these tails, even eventually. -/
theorem gaussian_bound_fails (A c T : ℝ) (hA : 0 < A) (hc : 0 < c) :
    ∃ t : ℝ, 1 ≤ t ∧ T ≤ t ∧
      Real.exp (-c * t ^ 2) < centeredExponential.real {x : ℝ | A * t ≤ |x|} := by
  let t := max (max T 1) ((A + 2) / c + 1)
  have ht1 : 1 ≤ t := (le_max_right T 1).trans (le_max_left _ _)
  have htT : T ≤ t := (le_max_left T 1).trans (le_max_left _ _)
  have htlarge : (A + 2) / c + 1 ≤ t := le_max_right _ _
  have hquot : (A + 2) / c < t := by linarith
  have hct : A + 2 < t * c := (div_lt_iff₀ hc).mp hquot
  have hpos : 0 < t := by linarith
  have hproduct := mul_lt_mul_of_pos_right hct hpos
  have hexponent : -c * t ^ 2 < -(A * t + 1) := by nlinarith
  refine ⟨t, ht1, htT, ?_⟩
  exact (Real.exp_lt_exp.mpr hexponent).trans_le
    (norm_tail_lower_bound (mul_nonneg hA.le (by linarith)))

end Conjecture7790
