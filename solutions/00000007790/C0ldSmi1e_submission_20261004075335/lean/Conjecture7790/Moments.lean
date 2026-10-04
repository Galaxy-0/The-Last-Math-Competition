import Conjecture7790.Definitions
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic

/-! Exact normalization and moments of the actual centered exponential measure. -/

noncomputable section
open MeasureTheory ProbabilityTheory Real Set

namespace Conjecture7790

private lemma gamma_one_toReal (x : ℝ) :
    (gammaPDF 1 1 x).toReal = if 0 ≤ x then Real.exp (-x) else 0 := by
  unfold gammaPDF gammaPDFReal
  split_ifs <;> simp [Real.exp_nonneg]

private lemma integrable_exp_one_iff (g : ℝ → ℝ) :
    Integrable g (expMeasure 1) ↔
      IntegrableOn (fun x => Real.exp (-x) * g x) (Ioi 0) := by
  have hm : Measurable (gammaPDF 1 1) := (measurable_gammaPDFReal 1 1).ennreal_ofReal
  rw [expMeasure, gammaMeasure,
    integrable_withDensity_iff_integrable_smul'
      hm
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp_rw [gamma_one_toReal, smul_eq_mul, ite_mul, zero_mul]
  change Integrable ((Ici (0 : ℝ)).indicator (fun x => Real.exp (-x) * g x)) ↔ _
  rw [integrable_indicator_iff measurableSet_Ici, integrableOn_Ici_iff_integrableOn_Ioi]

private lemma integral_exp_one (g : ℝ → ℝ) :
    (∫ x, g x ∂expMeasure 1) = ∫ x in Ioi 0, Real.exp (-x) * g x := by
  have hm : Measurable (gammaPDF 1 1) := (measurable_gammaPDFReal 1 1).ennreal_ofReal
  rw [expMeasure, gammaMeasure,
    integral_withDensity_eq_integral_toReal_smul
      hm
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp_rw [gamma_one_toReal, smul_eq_mul, ite_mul, zero_mul]
  change (∫ x, (Ici (0 : ℝ)).indicator (fun x => Real.exp (-x) * g x) x) = _
  rw [integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi]

/-- Every natural moment of the rate-one exponential distribution is integrable. -/
theorem exponential_integrable_pow (n : ℕ) :
    Integrable (fun x : ℝ => x ^ n) (expMeasure 1) := by
  rw [integrable_exp_one_iff]
  simpa using (Real.GammaIntegral_convergent (s := (n : ℝ) + 1) (by positivity))

/-- The natural moments of the rate-one exponential distribution are factorials. -/
theorem exponential_integral_pow (n : ℕ) :
    (∫ x : ℝ, x ^ n ∂expMeasure 1) = (n.factorial : ℝ) := by
  rw [integral_exp_one]
  simpa [mul_comm, Real.Gamma_nat_eq_factorial] using
    (Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (n : ℝ) + 1) (r := 1)
      (by positivity) (by norm_num))

/-- Translation preserves the normalization of the exponential law. -/
instance centeredExponential_isProbabilityMeasure : IsProbabilityMeasure centeredExponential := by
  letI : IsProbabilityMeasure (expMeasure 1) :=
    isProbabilityMeasureExponential (by norm_num)
  exact isProbabilityMeasure_map (measurable_id.sub_const 1).aemeasurable

theorem centeredExponential_integrable_id :
    Integrable (fun x : ℝ => x) centeredExponential := by
  rw [centeredExponential, integrable_map_measure (μ := expMeasure 1)
    (f := fun y : ℝ => y - 1) (g := fun x : ℝ => x) measurable_id.aestronglyMeasurable
    (measurable_id.sub_const 1).aemeasurable]
  have hi : Integrable (fun x : ℝ => x) (expMeasure 1) := by
    simpa using exponential_integrable_pow 1
  have hc : Integrable (fun _ : ℝ => (1 : ℝ)) (expMeasure 1) := by
    simpa using exponential_integrable_pow 0
  exact hi.sub hc

theorem centeredExponential_integrable_sq :
    Integrable (fun x : ℝ => x ^ 2) centeredExponential := by
  rw [centeredExponential, integrable_map_measure (μ := expMeasure 1)
    (f := fun y : ℝ => y - 1) (g := fun x : ℝ => x ^ 2)
    (measurable_id.pow_const 2).aestronglyMeasurable
    (measurable_id.sub_const 1).aemeasurable]
  have hi : Integrable (fun x : ℝ => x) (expMeasure 1) := by
    simpa using exponential_integrable_pow 1
  have hc : Integrable (fun _ : ℝ => (1 : ℝ)) (expMeasure 1) := by
    simpa using exponential_integrable_pow 0
  convert ((exponential_integrable_pow 2).sub (hi.const_mul 2)).add hc using 1
  ext x
  simp only [Function.comp_apply, Pi.add_apply, Pi.sub_apply]
  ring

theorem centeredExponential_integral_id :
    (∫ x : ℝ, x ∂centeredExponential) = 0 := by
  rw [centeredExponential, integral_map (μ := expMeasure 1)
    (φ := fun y : ℝ => y - 1) (f := fun x : ℝ => x)
    (measurable_id.sub_const 1).aemeasurable
    measurable_id.aestronglyMeasurable]
  have hi : Integrable (fun x : ℝ => x) (expMeasure 1) := by
    simpa using exponential_integrable_pow 1
  have hc : Integrable (fun _ : ℝ => (1 : ℝ)) (expMeasure 1) := by
    simpa using exponential_integrable_pow 0
  rw [integral_sub hi hc]
  have h1 := exponential_integral_pow 1
  have h0 := exponential_integral_pow 0
  simp only [pow_one, pow_zero, Nat.factorial_one, Nat.factorial_zero, Nat.cast_one] at h1 h0
  rw [h1, h0, sub_self]

theorem centeredExponential_integral_sq :
    (∫ x : ℝ, x ^ 2 ∂centeredExponential) = 1 := by
  rw [centeredExponential, integral_map (μ := expMeasure 1)
    (φ := fun y : ℝ => y - 1) (f := fun x : ℝ => x ^ 2)
    (measurable_id.sub_const 1).aemeasurable
    (measurable_id.pow_const 2).aestronglyMeasurable]
  have hi : Integrable (fun x : ℝ => x) (expMeasure 1) := by
    simpa using exponential_integrable_pow 1
  have hc : Integrable (fun _ : ℝ => (1 : ℝ)) (expMeasure 1) := by
    simpa using exponential_integrable_pow 0
  have hm : Integrable (fun x : ℝ => 2 * x) (expMeasure 1) := hi.const_mul 2
  have hs : Integrable (fun x : ℝ => x ^ 2 - 2 * x) (expMeasure 1) :=
    (exponential_integrable_pow 2).sub hm
  calc
    (∫ x : ℝ, (x - 1) ^ 2 ∂expMeasure 1) =
        ∫ x : ℝ, (x ^ 2 - 2 * x) + 1 ∂expMeasure 1 := by
      apply integral_congr_ae
      filter_upwards with x
      ring
    _ = (∫ x : ℝ, (x ^ 2 - 2 * x) ∂expMeasure 1) +
        ∫ _ : ℝ, (1 : ℝ) ∂expMeasure 1 := integral_add hs hc
    _ = ((∫ x : ℝ, x ^ 2 ∂expMeasure 1) -
        ∫ x : ℝ, 2 * x ∂expMeasure 1) +
        ∫ _ : ℝ, (1 : ℝ) ∂expMeasure 1 := by
      rw [integral_sub (exponential_integrable_pow 2) hm]
    _ = 1 := by
      rw [integral_const_mul]
      have h1 := exponential_integral_pow 1
      have h0 := exponential_integral_pow 0
      simp only [pow_one, pow_zero, Nat.factorial_one, Nat.factorial_zero, Nat.cast_one] at h1 h0
      rw [exponential_integral_pow 2, h1, h0]
      norm_num

/-- The distribution has zero mean and unit second moment, with both integrals integrable. -/
theorem centeredExponential_isIsotropic : IsIsotropic centeredExponential :=
  ⟨centeredExponential_integrable_id, centeredExponential_integrable_sq,
    centeredExponential_integral_id, centeredExponential_integral_sq⟩

end Conjecture7790
