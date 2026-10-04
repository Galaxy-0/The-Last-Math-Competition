import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

noncomputable section

namespace Conjecture2802

/-- An auxiliary real expression; its equality with the actual convex dual is proved separately. -/
def binaryRate (x : ℝ) : ℝ :=
  Real.log 2 + x * Real.log x + (1 - x) * Real.log (1 - x)

/-- The exponential tilt attaining the Bernoulli dual objective in the open interval. -/
def optimalTilt (x : ℝ) : ℝ := Real.log x - Real.log (1 - x)

/-- Every real tilt is bounded by the explicit interior expression. -/
theorem dual_objective_le_binaryRate (x t : ℝ) (hx : 0 < x) (hx1 : x < 1) :
    t*x - Real.log ((1 + Real.exp t) / 2) ≤ binaryRate x := by
  have hy : 0 < 1 - x := sub_pos.mpr hx1
  have hc := strictConcaveOn_log_Ioi.concaveOn.2
    (show Real.exp t / x ∈ Set.Ioi 0 from div_pos (Real.exp_pos t) hx)
    (show 1 / (1-x) ∈ Set.Ioi 0 from div_pos zero_lt_one hy)
    hx.le hy.le (show x + (1-x) = 1 by ring)
  simp only [smul_eq_mul] at hc
  have hs : x * (Real.exp t / x) + (1-x) * (1/(1-x)) = Real.exp t + 1 := by
    field_simp
  rw [hs, Real.log_div (Real.exp_ne_zero t) hx.ne',
    Real.log_div one_ne_zero hy.ne', Real.log_exp, Real.log_one] at hc
  rw [Real.log_div (by positivity) (by norm_num)]
  rw [add_comm 1 (Real.exp t)]
  dsimp [binaryRate]
  nlinarith

theorem exp_optimalTilt (x : ℝ) (hx : 0 < x) (hx1 : x < 1) :
    Real.exp (optimalTilt x) = x / (1-x) := by
  rw [optimalTilt, Real.exp_sub, Real.exp_log hx, Real.exp_log (sub_pos.mpr hx1)]

/-- This specific actual tilt attains the upper bound. -/
theorem dual_objective_optimalTilt (x : ℝ) (hx : 0 < x) (hx1 : x < 1) :
    optimalTilt x * x - Real.log ((1 + Real.exp (optimalTilt x)) / 2) = binaryRate x := by
  have hy : 0 < 1-x := sub_pos.mpr hx1
  have hden : (1 + Real.exp (optimalTilt x)) / 2 = 1 / (2 * (1-x)) := by
    rw [exp_optimalTilt x hx hx1]
    field_simp
    ring
  rw [hden, Real.log_div one_ne_zero (by positivity), Real.log_one,
    Real.log_mul (by norm_num) hy.ne']
  dsimp [optimalTilt, binaryRate]
  ring

/-- The expression agrees with binary relative entropy against the fair law. -/
theorem binaryRate_eq_relativeEntropy (x : ℝ) (hx : 0 < x) (hx1 : x < 1) :
    binaryRate x = x * Real.log (2*x) + (1-x) * Real.log (2*(1-x)) := by
  rw [Real.log_mul (by norm_num) hx.ne', Real.log_mul (by norm_num) (sub_pos.mpr hx1).ne']
  dsimp [binaryRate]
  ring

end Conjecture2802
