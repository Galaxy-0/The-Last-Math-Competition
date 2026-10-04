import Definitions
import Mathlib.Data.Real.Pi.Bounds
import Mathlib.Tactic

namespace Conjecture420

lemma rho_nonneg {x : ℝ} (hx : x ∈ angularInterval) : 0 ≤ rho x := by
  have hc : 0 ≤ Real.cos x := Real.cos_nonneg_of_mem_Icc (by
    simpa only [angularInterval, leftEndpoint, rightEndpoint, neg_div] using hx)
  exact mul_nonneg
    (mul_nonneg (div_nonneg (by norm_num) Real.pi_pos.le) hc) (Real.sqrt_nonneg _)

/-- The exact total mass is strictly greater than one. -/
lemma mass_gt_one : (1 : ℝ) < 8 * Real.sqrt 2 / (3 * Real.pi) := by
  have hs : (7 / 5 : ℝ) < Real.sqrt 2 := by
    have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have hnonneg := Real.sqrt_nonneg (2 : ℝ)
    nlinarith
  apply (lt_div_iff₀ (by positivity : (0 : ℝ) < 3 * Real.pi)).mpr
  nlinarith [Real.pi_lt_d2]

end Conjecture420
