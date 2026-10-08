import Mathlib.Probability.Variance
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Conjecture6953

/-- Five independent fair binary outcomes, represented as the full Cartesian product. -/
abbrev Ω := Fin 2 × Fin 2 × Fin 2 × Fin 2 × Fin 2

instance : MeasurableSpace Ω := ⊤
instance : MeasurableSingletonClass Ω := ⟨fun _ => trivial⟩

/-- Each of the 32 outcomes has mass 1/32. -/
def μ : Measure Ω := (1 / 32 : ℝ≥0∞) • Measure.count

theorem mass_one : μ Set.univ = 1 := by
  norm_num [μ, Measure.smul_apply, Measure.count_univ, ENat.card_eq_coe_fintype_card,
    Fintype.card_prod, Fintype.card_fin]
  exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)

instance : IsProbabilityMeasure μ := ⟨mass_one⟩

theorem outcome_mass (ω : Ω) : μ {ω} = 1 / 32 := by
  simp [μ, Measure.smul_apply]

def sign (b : Fin 2) : ℝ := if b = 0 then -1 else 1

def sample (ω : Ω) : Fin 5 → Fin 2 := ![ω.1, ω.2.1, ω.2.2.1, ω.2.2.2.1, ω.2.2.2.2]

theorem joint_outcome_mass (a b c d e : Fin 2) :
    μ {ω | sample ω 0 = a ∧ sample ω 1 = b ∧ sample ω 2 = c ∧
      sample ω 3 = d ∧ sample ω 4 = e} = (1 / 2 : ℝ≥0∞) ^ 5 := by
  have hs : {ω | sample ω 0 = a ∧ sample ω 1 = b ∧ sample ω 2 = c ∧
      sample ω 3 = d ∧ sample ω 4 = e} = {(a, b, c, d, e)} := by
    ext ω
    simp [sample, Prod.ext_iff, and_assoc]
  rw [hs, outcome_mass]
  norm_num [div_pow]
  rw [← ENNReal.inv_pow]
  norm_num

/-- Equal stratum weights; n samples from {-1,1}, and 5-n from {-2,2}. -/
def estimator (n : ℕ) (ω : Ω) : ℝ :=
  ((∑ i : Fin 5, if i.val < n then sign (sample ω i) else 0) / n +
   (∑ i : Fin 5, if n ≤ i.val then 2 * sign (sample ω i) else 0) / (5 - n : ℕ)) / 2

def Admissible (n : ℕ) : Prop := 0 < n ∧ n < 5

def Optimal (n : ℕ) : Prop := Admissible n ∧
  ∀ m : ℕ, Admissible m → variance (estimator n) μ ≤ variance (estimator m) μ

theorem integral_as_sum (X : Ω → ℝ) : (∫ ω, X ω ∂μ) = (∑ ω, X ω) / 32 := by
  rw [μ, integral_smul_measure, integral_count]
  norm_num
  ring

theorem variance_as_sum (X : Ω → ℝ) :
    variance X μ = (∑ ω, (X ω - (∑ τ, X τ) / 32) ^ 2) / 32 := by
  rw [variance_eq_integral (by exact (measurable_of_finite X).aemeasurable),
    integral_as_sum, integral_as_sum]

theorem first_stratum_mean : (∫ ω, sign (sample ω 0) ∂μ) = 0 := by
  rw [integral_as_sum]
  norm_num [Fintype.sum_prod_type, Fin.sum_univ_succ, sample, sign]

theorem second_stratum_mean : (∫ ω, 2 * sign (sample ω 0) ∂μ) = 0 := by
  rw [integral_as_sum]
  norm_num [Fintype.sum_prod_type, Fin.sum_univ_succ, sample, sign]

theorem first_stratum_variance : variance (fun ω => sign (sample ω 0)) μ = 1 := by
  rw [variance_eq_integral (by exact (measurable_of_finite _).aemeasurable),
    first_stratum_mean, integral_as_sum]
  norm_num [Fintype.sum_prod_type, Fin.sum_univ_succ, sample, sign]

theorem second_stratum_variance : variance (fun ω => 2 * sign (sample ω 0)) μ = 4 := by
  rw [variance_eq_integral (by exact (measurable_of_finite _).aemeasurable),
    second_stratum_mean, integral_as_sum]
  norm_num [Fintype.sum_prod_type, Fin.sum_univ_succ, sample, sign]

theorem allocation_one_is_variance_proportional :
    (1 : ℝ) / (5 - 1 : ℕ) =
      variance (fun ω => sign (sample ω 0)) μ /
      variance (fun ω => 2 * sign (sample ω 0)) μ := by
  rw [first_stratum_variance, second_stratum_variance]
  norm_num

theorem estimator_one_unbiased : (∫ ω, estimator 1 ω ∂μ) = 0 := by
  rw [integral_as_sum]
  norm_num [Fintype.sum_prod_type, Fin.sum_univ_succ, estimator, sample, sign]

theorem estimator_two_unbiased : (∫ ω, estimator 2 ω ∂μ) = 0 := by
  rw [integral_as_sum]
  norm_num [Fintype.sum_prod_type, Fin.sum_univ_succ, estimator, sample, sign]

theorem variance_one : variance (estimator 1) μ = 1 / 2 := by
  rw [variance_eq_integral (by exact (measurable_of_finite _).aemeasurable),
    estimator_one_unbiased, integral_as_sum]
  norm_num [Fintype.sum_prod_type, Fin.sum_univ_succ, estimator, sample, sign]

theorem variance_two : variance (estimator 2) μ = 11 / 24 := by
  rw [variance_eq_integral (by exact (measurable_of_finite _).aemeasurable),
    estimator_two_unbiased, integral_as_sum]
  norm_num [Fintype.sum_prod_type, Fin.sum_univ_succ, estimator, sample, sign]

theorem variance_proportional_allocation_not_optimal : ¬ Optimal 1 := by
  intro h
  have hv := h.2 2 (by norm_num [Admissible])
  rw [variance_one, variance_two] at hv
  norm_num at hv

#print axioms mass_one
#print axioms outcome_mass
#print axioms joint_outcome_mass
#print axioms allocation_one_is_variance_proportional
#print axioms integral_as_sum
#print axioms variance_as_sum
#print axioms estimator_one_unbiased
#print axioms estimator_two_unbiased
#print axioms variance_one
#print axioms variance_two
#print axioms variance_proportional_allocation_not_optimal

end Conjecture6953
