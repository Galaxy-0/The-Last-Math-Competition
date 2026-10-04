import Definitions
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic

namespace Conjecture420
open MeasureTheory

/-- The proposed density is continuous, including both endpoints. -/
theorem rho_continuous : Continuous rho := by
  unfold rho
  fun_prop

/-- Hence it is integrable over the compact angular support. -/
theorem rho_integrableOn : IntegrableOn rho angularInterval := by
  exact rho_continuous.integrableOn_Icc

theorem rho_intervalIntegrable : IntervalIntegrable rho volume leftEndpoint rightEndpoint :=
  rho_continuous.intervalIntegrable _ _

private theorem integral_sqrt_zero_two :
    (∫ x in (0 : ℝ)..2, Real.sqrt x) = 4 * Real.sqrt 2 / 3 := by
  simp_rw [Real.sqrt_eq_rpow]
  rw [integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < 1 / 2))]
  rw [Real.rpow_add_one (by norm_num : (2 : ℝ) ≠ 0)]
  norm_num
  ring

/-- Exact evaluation by the substitution u = 1 - sin(theta). -/
theorem rho_intervalIntegral :
    (∫ x in leftEndpoint..rightEndpoint, rho x) =
      8 * Real.sqrt 2 / (3 * Real.pi) := by
  have hsubst :
      (∫ x in leftEndpoint..rightEndpoint,
        Real.sqrt (1 - Real.sin x) * (-Real.cos x)) =
        ∫ y in (2 : ℝ)..0, Real.sqrt y := by
    have hh := intervalIntegral.integral_comp_mul_deriv
      (a := leftEndpoint) (b := rightEndpoint)
      (f := fun x : ℝ => 1 - Real.sin x) (f' := fun x => -Real.cos x)
      (g := Real.sqrt)
      (fun x _ => (Real.hasDerivAt_sin x).const_sub 1)
      Real.continuous_cos.neg.continuousOn Real.continuous_sqrt
    simpa [Function.comp_def, leftEndpoint, rightEndpoint, neg_div,
      Real.sin_neg, Real.sin_pi_div_two, one_add_one_eq_two] using hh
  calc
    (∫ x in leftEndpoint..rightEndpoint, rho x) =
        -(2 / Real.pi) * (∫ x in leftEndpoint..rightEndpoint,
          Real.sqrt (1 - Real.sin x) * (-Real.cos x)) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro x _
      dsimp [rho]
      ring
    _ = 8 * Real.sqrt 2 / (3 * Real.pi) := by
      rw [hsubst, intervalIntegral.integral_symm, integral_sqrt_zero_two]
      ring

/-- The set integral on the closed angular interval has the same exact value. -/
theorem rho_setIntegral :
    (∫ x in angularInterval, rho x) = 8 * Real.sqrt 2 / (3 * Real.pi) := by
  have hab : leftEndpoint ≤ rightEndpoint := by
    unfold leftEndpoint rightEndpoint
    linarith [Real.pi_pos]
  rw [angularInterval, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hab, rho_intervalIntegral]


end Conjecture420
