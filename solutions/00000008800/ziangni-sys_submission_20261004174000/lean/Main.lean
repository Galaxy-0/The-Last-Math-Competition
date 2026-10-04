import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Variance
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology BigOperators
noncomputable section
namespace BenchmarkVariance
abbrev Seed := Fin 2
instance : MeasurableSpace Seed := ⊤
instance : MeasurableSingletonClass Seed := ⟨fun _ => trivial⟩
def seedPMF : PMF Seed := PMF.ofFintype (fun _ => (1/2 : ℝ≥0∞)) (by
  norm_num
  exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num))
def ν : Measure Seed := seedPMF.toMeasure
instance : IsProbabilityMeasure ν := inferInstanceAs (IsProbabilityMeasure seedPMF.toMeasure)
def A : Matrix Seed Seed ℝ := !![1, 0; 0, 0]
def sample (j : Seed) : ℝ := 2 * A j j

theorem seed_mass (j : Seed) : ν {j} = (1/2 : ℝ≥0∞) := by
  change seedPMF.toMeasure {j} = _
  rw [PMF.toMeasure_apply_singleton seedPMF j (MeasurableSet.singleton j)]
  rfl
theorem sample_measurable : Measurable sample := measurable_of_countable sample

theorem seed_unbiased : (∫ j, sample j ∂ν) = Matrix.trace A := by
  norm_num [ν, PMF.integral_eq_sum, seedPMF, sample, A, Matrix.trace, Fin.sum_univ_two]
theorem trace_one : Matrix.trace A = 1 := by norm_num [A, Matrix.trace, Fin.sum_univ_two]
theorem seed_variance : variance sample ν = 1 := by
  rw [variance_eq_integral sample_measurable.aemeasurable, seed_unbiased, trace_one]
  norm_num [ν, PMF.integral_eq_sum, seedPMF, sample, A, Fin.sum_univ_two]

abbrev Ω (m : ℕ) := Fin m → Seed
def μ (m : ℕ) : Measure (Ω m) := Measure.pi (fun _ : Fin m => ν)
instance (m : ℕ) : IsProbabilityMeasure (μ m) := inferInstanceAs
  (IsProbabilityMeasure (Measure.pi (fun _ : Fin m => ν)))

theorem marginal (m : ℕ) (i : Fin m) : (μ m).map (Function.eval i) = ν := by
  classical
  ext s hs
  rw [Measure.map_apply (measurable_pi_apply i) hs]
  rw [Set.eval_preimage, μ, Measure.pi_pi]
  simp [Function.update_apply, apply_ite]

theorem seeds_independent (m : ℕ) : iIndepFun (fun i : Fin m => Function.eval i) (μ m) := by
  rw [iIndepFun_iff_map_fun_eq_pi_map (fun i => (measurable_pi_apply i).aemeasurable)]
  simp only [marginal]
  change (μ m).map id = μ m
  exact Measure.map_id

def X (m : ℕ) (i : Fin m) (ω : Ω m) : ℝ := sample (ω i)

theorem samples_independent (m : ℕ) : iIndepFun (X m) (μ m) :=
  (seeds_independent m).comp (fun _ => sample) (fun _ => sample_measurable)

theorem sample_distribution (m : ℕ) (i : Fin m) : IdentDistrib (X m i) sample (μ m) ν := by
  have h : IdentDistrib (Function.eval i) id (μ m) ν :=
    ⟨(measurable_pi_apply i).aemeasurable, measurable_id.aemeasurable, by
      rw [marginal, Measure.map_id]⟩
  exact h.comp sample_measurable

theorem X_memLp (m : ℕ) (i : Fin m) : MemLp (X m i) 2 (μ m) :=
  ⟨(sample_measurable.comp (measurable_pi_apply i)).aestronglyMeasurable,
    eLpNorm_lt_top_of_finite⟩

def average (m : ℕ) (ω : Ω m) : ℝ := (m : ℝ)⁻¹ * ∑ i, X m i ω

theorem sum_variance (m : ℕ) : variance (∑ i : Fin m, X m i) (μ m) = m := by
  rw [IndepFun.variance_sum (fun i _ => X_memLp m i)
    (fun i _ j _ hij => (samples_independent m).indepFun hij)]
  simp only [(sample_distribution m _).variance_eq, seed_variance,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]

theorem average_variance (m : ℕ) (hm : 0 < m) : variance (average m) (μ m) = 1 / m := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have he : average m = fun ω => (m : ℝ)⁻¹ * (∑ i : Fin m, X m i) ω := by
    funext ω
    simp [average]
  rw [he, variance_mul, sum_variance]
  field_simp
  ring

theorem average_unbiased (m : ℕ) (hm : 0 < m) : (∫ ω, average m ω ∂μ m) = Matrix.trace A := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hi (i : Fin m) : Integrable (X m i) (μ m) := (X_memLp m i).integrable (by norm_num)
  have hx (i : Fin m) : (∫ ω, X m i ω ∂μ m) = 1 :=
    (sample_distribution m i).integral_eq.trans (seed_unbiased.trans trace_one)
  simp only [average, integral_const_mul, integral_finset_sum _ (fun i _ => hi i), hx,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
    inv_mul_cancel₀ hm0, trace_one]

def varianceRatio (n : ℕ) : ℝ :=
  variance (average (n+1)) (μ (n+1)) / (1 / Real.sqrt (n+1 : ℝ))

theorem ratio_formula (n : ℕ) : varianceRatio n = Real.sqrt ((n+1 : ℝ)⁻¹) := by
  rw [varianceRatio, average_variance _ (by omega)]
  simp only [Nat.cast_add, Nat.cast_one, div_div_eq_mul_div, one_mul]
  rw [div_one, one_div, mul_comm, ← div_eq_mul_inv, Real.sqrt_div_self, Real.sqrt_inv]

theorem ratio_tends_zero : Tendsto varianceRatio atTop (𝓝 0) := by
  have hn : Tendsto (fun n : ℕ => (n+1 : ℝ)) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have hi := tendsto_inv_atTop_zero.comp hn
  have he : varianceRatio = fun n : ℕ => Real.sqrt ((n+1 : ℝ)⁻¹) := funext ratio_formula
  rw [he]
  simpa only [Function.comp_def, Real.sqrt_zero] using Real.continuous_sqrt.continuousAt.tendsto.comp hi

theorem no_positive_root_lower_bound : ¬ ∃ c : ℝ, 0 < c ∧
    ∀ᶠ n : ℕ in atTop, c / Real.sqrt (n+1 : ℝ) ≤ variance (average (n+1)) (μ (n+1)) := by
  rintro ⟨c, hc, hb⟩
  have hr := (tendsto_order.1 ratio_tends_zero).2 c hc
  obtain ⟨n, hn, hbn⟩ := (hr.and hb).exists
  have hs : 0 < Real.sqrt (n+1 : ℝ) := Real.sqrt_pos.2 (by positivity)
  have hp : 0 < 1 / Real.sqrt (n+1 : ℝ) := one_div_pos.mpr hs
  have hl : c ≤ varianceRatio n := by
    rw [varianceRatio, le_div_iff₀ hp]
    simpa [div_eq_mul_inv] using hbn
  exact (not_lt_of_ge hl) hn

#print axioms seed_mass
#print axioms seed_unbiased
#print axioms seed_variance
#print axioms seeds_independent
#print axioms samples_independent
#print axioms sample_distribution
#print axioms average_unbiased
#print axioms average_variance
#print axioms ratio_tends_zero
#print axioms no_positive_root_lower_bound
end BenchmarkVariance
