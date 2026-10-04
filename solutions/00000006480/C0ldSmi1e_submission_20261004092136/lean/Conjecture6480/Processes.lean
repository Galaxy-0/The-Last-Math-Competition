import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Tactic

/-!
# An explicit pair with equal covariances and different maximum laws

All expectations and probabilities below use the measure of the uniform PMF on
eight outcomes. The first process lists all sign triples; the second replaces
its third coordinate by the product of the first two coordinates.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal NNReal Classical

namespace Conjecture6480

abbrev Ω := Fin 8

instance : MeasurableSpace Ω := ⊤
instance : MeasurableSingletonClass Ω := ⟨fun _ => trivial⟩

def μ : Measure Ω := (PMF.uniformOfFintype Ω).toMeasure

instance μ_probability : IsProbabilityMeasure μ := by
  unfold μ
  infer_instance

/-- The eight outcomes are `+++`, `++-`, `+-+`, `+--`, `-++`, `-+-`, `--+`, `---`. -/
def X : Fin 3 → Ω → ℝ :=
  ![![1, 1, 1, 1, -1, -1, -1, -1],
    ![1, 1, -1, -1, 1, 1, -1, -1],
    ![1, -1, 1, -1, 1, -1, 1, -1]]

def Y : Fin 3 → Ω → ℝ := ![X 0, X 1, fun ω => X 0 ω * X 1 ω]

def mean (Z : Fin 3 → Ω → ℝ) (i : Fin 3) : ℝ := ∫ ω, Z i ω ∂μ

/-- Covariance uses the actual centered Bochner integral. -/
def covarianceMatrix (Z : Fin 3 → Ω → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => ∫ ω, (Z i ω - mean Z i) * (Z j ω - mean Z j) ∂μ

def jointLaw (Z : Fin 3 → Ω → ℝ) : Measure (Fin 3 → ℝ) :=
  μ.map (fun ω i => Z i ω)

def peak (Z : Fin 3 → Ω → ℝ) (ω : Ω) : ℝ :=
  max (Z 0 ω) (max (Z 1 ω) (Z 2 ω))

def extremeLaw (Z : Fin 3 → Ω → ℝ) : Measure ℝ := μ.map (peak Z)

theorem measurable_on_Ω {α : Type*} [MeasurableSpace α] (f : Ω → α) :
    Measurable f := measurable_of_finite f

theorem integrable_on_Ω (f : Ω → ℝ) : Integrable f μ := Integrable.of_finite

theorem coordinates_measurable (Z : Fin 3 → Ω → ℝ) (i : Fin 3) :
    Measurable (Z i) := measurable_on_Ω _

theorem coordinates_integrable (Z : Fin 3 → Ω → ℝ) (i : Fin 3) :
    Integrable (Z i) μ := integrable_on_Ω _

theorem covariance_integrable (Z : Fin 3 → Ω → ℝ) (i j : Fin 3) :
    Integrable (fun ω => (Z i ω - mean Z i) * (Z j ω - mean Z j)) μ :=
  integrable_on_Ω _

theorem peak_measurable (Z : Fin 3 → Ω → ℝ) : Measurable (peak Z) :=
  measurable_on_Ω _

theorem peak_integrable (Z : Fin 3 → Ω → ℝ) : Integrable (peak Z) μ :=
  integrable_on_Ω _

theorem joint_measurable (Z : Fin 3 → Ω → ℝ) : Measurable (fun ω i => Z i ω) :=
  measurable_on_Ω _

instance jointLaw_probability (Z : Fin 3 → Ω → ℝ) : IsProbabilityMeasure (jointLaw Z) :=
  isProbabilityMeasure_map (joint_measurable Z).aemeasurable

instance extremeLaw_probability (Z : Fin 3 → Ω → ℝ) : IsProbabilityMeasure (extremeLaw Z) :=
  isProbabilityMeasure_map (peak_measurable Z).aemeasurable

theorem integral_uniform (f : Ω → ℝ) :
    (∫ ω, f ω ∂μ) = ∑ ω : Ω, (1 / 8 : ℝ) * f ω := by
  rw [μ, PMF.integral_eq_sum]
  simp [PMF.uniformOfFintype_apply, Fintype.card_fin]

theorem measure_uniform (s : Set Ω) :
    μ s = ∑ ω : Ω, if ω ∈ s then (1 / 8 : ℝ≥0∞) else 0 := by
  rw [μ, PMF.toMeasure_apply_fintype]
  simp [Set.indicator_apply, PMF.uniformOfFintype_apply, Fintype.card_fin]

theorem means_X (i : Fin 3) : mean X i = 0 := by
  fin_cases i <;> norm_num [mean, integral_uniform, X, Fin.sum_univ_succ]

theorem means_Y (i : Fin 3) : mean Y i = 0 := by
  fin_cases i <;> norm_num [mean, integral_uniform, Y, X, Fin.sum_univ_succ]

theorem covariance_X : covarianceMatrix X = 1 := by
  ext i j
  simp only [covarianceMatrix, means_X, sub_zero, integral_uniform]
  fin_cases i <;> fin_cases j <;> norm_num [X, Fin.sum_univ_succ, Matrix.one_apply]

theorem covariance_Y : covarianceMatrix Y = 1 := by
  ext i j
  simp only [covarianceMatrix, means_Y, sub_zero, integral_uniform]
  fin_cases i <;> fin_cases j <;> norm_num [Y, X, Fin.sum_univ_succ, Matrix.one_apply]

theorem coordinate0_atom_X :
    (μ.map (X 0)) {(-1 : ℝ)} = (1 / 2 : ℝ≥0∞) := by
  rw [Measure.map_apply (coordinates_measurable X 0) (measurableSet_singleton _),
    measure_uniform]
  norm_num [X, Fin.sum_univ_succ]
  apply (ENNReal.toReal_eq_toReal (by norm_num [div_eq_mul_inv, ENNReal.mul_eq_top]) (by norm_num [div_eq_mul_inv, ENNReal.mul_eq_top])).mp
  norm_num [ENNReal.toReal_add, div_eq_mul_inv, ENNReal.mul_eq_top]

theorem coordinate0_atom_Y :
    (μ.map (Y 0)) {(-1 : ℝ)} = (1 / 2 : ℝ≥0∞) := by
  simpa only [Y, Matrix.cons_val_zero] using coordinate0_atom_X

theorem coordinate_atom_X (i : Fin 3) :
    (μ.map (X i)) {(-1 : ℝ)} = (1 / 2 : ℝ≥0∞) := by
  rw [Measure.map_apply (coordinates_measurable X i) (measurableSet_singleton _),
    measure_uniform]
  fin_cases i <;> norm_num [X, Fin.sum_univ_succ]
  all_goals
    apply (ENNReal.toReal_eq_toReal (by norm_num) (by norm_num)).mp
    norm_num [ENNReal.toReal_add]

theorem coordinate_atom_Y (i : Fin 3) :
    (μ.map (Y i)) {(-1 : ℝ)} = (1 / 2 : ℝ≥0∞) := by
  rw [Measure.map_apply (coordinates_measurable Y i) (measurableSet_singleton _),
    measure_uniform]
  fin_cases i <;> norm_num [Y, X, Fin.sum_univ_succ]
  all_goals
    apply (ENNReal.toReal_eq_toReal (by norm_num) (by norm_num)).mp
    norm_num [ENNReal.toReal_add]

def allNegative : Fin 3 → ℝ := fun _ => -1

theorem joint_negative_X : jointLaw X {allNegative} = (1 / 8 : ℝ≥0∞) := by
  rw [jointLaw, Measure.map_apply (joint_measurable X) (measurableSet_singleton _),
    measure_uniform]
  norm_num [X, allNegative, Fin.sum_univ_succ, funext_iff, Fin.forall_fin_succ]

theorem joint_negative_Y : jointLaw Y {allNegative} = 0 := by
  rw [jointLaw, Measure.map_apply (joint_measurable Y) (measurableSet_singleton _),
    measure_uniform]
  norm_num [Y, X, allNegative, Fin.sum_univ_succ, funext_iff, Fin.forall_fin_succ]

theorem extreme_negative_X : extremeLaw X {(-1 : ℝ)} = (1 / 8 : ℝ≥0∞) := by
  rw [extremeLaw, Measure.map_apply (peak_measurable X) (measurableSet_singleton _),
    measure_uniform]
  norm_num [peak, X, Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]

theorem extreme_negative_Y : extremeLaw Y {(-1 : ℝ)} = 0 := by
  rw [extremeLaw, Measure.map_apply (peak_measurable Y) (measurableSet_singleton _),
    measure_uniform]
  norm_num [peak, Y, X, Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]

theorem peak_Y_eq_one (ω : Ω) : peak Y ω = 1 := by
  fin_cases ω <;> norm_num [peak, Y, X, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]

theorem extremeLaw_Y : extremeLaw Y = Measure.dirac (1 : ℝ) := by
  ext s hs
  rw [extremeLaw, Measure.map_apply (peak_measurable Y) hs, Measure.dirac_apply' _ hs,
    measure_uniform]
  by_cases h : (1 : ℝ) ∈ s
  · norm_num [peak_Y_eq_one, Set.indicator_apply, h, Fin.sum_univ_succ]
    apply (ENNReal.toReal_eq_toReal (by norm_num [div_eq_mul_inv, ENNReal.mul_eq_top]) (by norm_num [div_eq_mul_inv, ENNReal.mul_eq_top])).mp
    norm_num [ENNReal.toReal_add, div_eq_mul_inv, ENNReal.mul_eq_top]
  · simp [peak_Y_eq_one, Set.indicator_apply, h]

theorem extremeLaw_X :
    extremeLaw X = (1 / 8 : ℝ≥0∞) • Measure.dirac (-1 : ℝ) +
      (7 / 8 : ℝ≥0∞) • Measure.dirac (1 : ℝ) := by
  ext s hs
  rw [extremeLaw, Measure.map_apply (peak_measurable X) hs, measure_uniform,
    Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    Measure.dirac_apply' _ hs, Measure.dirac_apply' _ hs]
  by_cases hm : (-1 : ℝ) ∈ s <;> by_cases hp : (1 : ℝ) ∈ s <;>
    norm_num [peak, X, Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.vecHead,
      Matrix.vecTail, Set.indicator_apply, hm, hp]
  all_goals
    apply (ENNReal.toReal_eq_toReal (by norm_num [div_eq_mul_inv, ENNReal.mul_eq_top]) (by norm_num [div_eq_mul_inv, ENNReal.mul_eq_top])).mp
    norm_num [ENNReal.toReal_add, div_eq_mul_inv, ENNReal.mul_eq_top]

end Conjecture6480
