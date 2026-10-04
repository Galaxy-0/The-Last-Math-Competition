import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

/-! The exact proposed leading term outgrows every sequence bounded by `sqrt n`. -/

noncomputable section
open Filter
open scoped Topology

namespace Conjecture428

/-- The scale appearing verbatim in both versions of the conjecture. -/
def scale (n : ℕ) : ℝ := Real.sqrt (6 * (n : ℝ)) / Real.pi

/-- The displayed leading term of the conjectured expected Durfee size. -/
def mainTerm (n : ℕ) : ℝ := scale n * Real.log (scale n)

theorem scale_eq (n : ℕ) :
    scale n = (Real.sqrt 6 / Real.pi) * Real.sqrt (n : ℝ) := by
  rw [scale, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 6)]
  ring

theorem scale_coefficient_pos : 0 < Real.sqrt 6 / Real.pi := by positivity

theorem sqrt_nat_tendsto_atTop :
    Tendsto (fun n : ℕ => Real.sqrt (n : ℝ)) atTop atTop := by
  simpa only [Real.sqrt_eq_rpow] using
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)

theorem scale_tendsto_atTop : Tendsto scale atTop atTop := by
  change Tendsto (fun n => scale n) atTop atTop
  simpa only [scale_eq] using sqrt_nat_tendsto_atTop.const_mul_atTop scale_coefficient_pos

theorem eventually_two_sqrt_le_mainTerm :
    ∀ᶠ n : ℕ in atTop, 2 * Real.sqrt (n : ℝ) ≤ mainTerm n := by
  have hlog := (Real.tendsto_log_atTop.comp scale_tendsto_atTop).eventually_ge_atTop
    (2 / (Real.sqrt 6 / Real.pi))
  filter_upwards [hlog] with n hn
  have h : 2 ≤ Real.log (scale n) * (Real.sqrt 6 / Real.pi) :=
    (div_le_iff₀ scale_coefficient_pos).mp hn
  have hm := mul_le_mul_of_nonneg_right h (Real.sqrt_nonneg (n : ℝ))
  rw [scale_eq] at hm
  rw [mainTerm, scale_eq]
  nlinarith [hm]

/-- A deterministic square-root bound already makes the proposed excess diverge. -/
theorem mainTerm_sub_tendsto_atTop (f : ℕ → ℝ)
    (hf : ∀ n, f n ≤ Real.sqrt (n : ℝ)) :
    Tendsto (fun n => mainTerm n - f n) atTop atTop := by
  apply tendsto_atTop_mono' atTop _ sqrt_nat_tendsto_atTop
  filter_upwards [eventually_two_sqrt_le_mainTerm] with n hn
  linarith [hf n]

/-- No real constant can be the additive limiting correction. -/
theorem no_constant_correction (f : ℕ → ℝ)
    (hf : ∀ n, f n ≤ Real.sqrt (n : ℝ)) (c : ℝ) :
    ¬ Tendsto (fun n => f n - mainTerm n) atTop (𝓝 c) := by
  intro h
  have hneg : Tendsto (fun n => mainTerm n - f n) atTop (𝓝 (-c)) := by
    simpa only [neg_sub] using h.neg
  exact not_tendsto_nhds_of_tendsto_atTop (mainTerm_sub_tendsto_atTop f hf) (-c) hneg

end Conjecture428
