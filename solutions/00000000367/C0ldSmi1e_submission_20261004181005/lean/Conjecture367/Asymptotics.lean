import Conjecture367.Definitions
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

noncomputable section
open Filter
open scoped Topology

namespace Conjecture367

theorem third_pow_eq_exp (n : ℕ) :
    (1 / 3 : ℝ) ^ n = Real.exp (-Real.log 3 * (n : ℝ)) := by
  rw [mul_comm, Real.exp_nat_mul, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 3)]
  simp only [one_div]

/-- Exponential decay beats every real power along the full sequence. -/
theorem polynomial_mul_third_pow_tendsto (C : ℝ) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ C * (1 / 3 : ℝ) ^ n) atTop (𝓝 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero C
    (Real.log 3) (Real.log_pos (by norm_num : (1 : ℝ) < 3))).comp
      tendsto_natCast_atTop_atTop
  simpa only [third_pow_eq_exp] using h

theorem third_pow_eventually_lt_rpow_neg (C : ℝ) :
    ∀ᶠ n : ℕ in atTop, (1 / 3 : ℝ) ^ n < (n : ℝ) ^ (-C) := by
  have h := (polynomial_mul_third_pow_tendsto C).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [h, eventually_ge_atTop (1 : ℕ)] with n hn hn1
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hpow : 0 < (n : ℝ) ^ C := Real.rpow_pos_of_pos hnpos C
  rw [Real.rpow_neg hnpos.le, ← one_div]
  apply (lt_div_iff₀ hpow).2
  simpa only [mul_comm] using hn

end Conjecture367
