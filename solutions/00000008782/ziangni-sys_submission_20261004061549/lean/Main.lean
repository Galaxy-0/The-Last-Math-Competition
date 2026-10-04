import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.Variance
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical
noncomputable section
namespace HutchinsonCounterexample
abbrev Ω := Fin 2 × Fin 2
instance : MeasurableSpace Ω := ⊤
instance : MeasurableSingletonClass Ω := ⟨fun _ => trivial⟩
def law : PMF Ω := PMF.ofFintype (fun _ => (1 / 4 : ℝ≥0∞)) (by norm_num; exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num))
def μ : Measure Ω := law.toMeasure
instance : IsProbabilityMeasure μ := inferInstanceAs (IsProbabilityMeasure law.toMeasure)
def sign (i : Fin 2) : ℝ := ![-1, 1] i
def X (ω : Ω) : ℝ := sign ω.1
def Y (ω : Ω) : ℝ := sign ω.2
lemma mass (s : Set Ω) : μ s = ∑ ω : Ω, if ω ∈ s then (1/4 : ℝ≥0∞) else 0 := by
  classical
  simp only [μ, law, PMF.toMeasure_ofFintype_apply _ _ (show MeasurableSet s from trivial), tsum_fintype]
  rfl
lemma independent : IndepFun X Y μ := by
  classical
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  intro s t _ _
  simp only [mass, Fintype.sum_prod_type, Fin.sum_univ_two, Set.mem_inter_iff,
    Set.mem_preimage, X, Y, sign, Matrix.cons_val_zero, Matrix.cons_val_one]
  by_cases h₁ : (-1 : ℝ) ∈ s <;> by_cases h₂ : (1 : ℝ) ∈ s <;>
    by_cases h₃ : (-1 : ℝ) ∈ t <;> by_cases h₄ : (1 : ℝ) ∈ t <;>
    (simp only [h₁, h₂, h₃, h₄, and_true, and_false, true_and, false_and, ite_true, ite_false, add_zero, zero_add, mul_zero, zero_mul] <;> apply (ENNReal.toReal_eq_toReal (by simp [div_eq_mul_inv, ENNReal.mul_ne_top]) (by simp [div_eq_mul_inv, ENNReal.mul_ne_top])).mp <;> norm_num [ENNReal.toReal_add, div_eq_mul_inv])
lemma rademacher_X (a : ℝ) : μ {ω | X ω = a} =
    if a = -1 ∨ a = 1 then (1/2 : ℝ≥0∞) else 0 := by
  classical
  simp only [mass, Fintype.sum_prod_type, Fin.sum_univ_two, Set.mem_setOf_eq,
    X, sign, Matrix.cons_val_zero, Matrix.cons_val_one]
  by_cases h₁ : a = -1 <;> by_cases h₂ : a = 1 <;> (norm_num [h₁, h₂, eq_comm] <;> apply (ENNReal.toReal_eq_toReal (by simp [div_eq_mul_inv, ENNReal.mul_ne_top]) (by simp [div_eq_mul_inv, ENNReal.mul_ne_top])).mp <;> norm_num [ENNReal.toReal_add, div_eq_mul_inv])
lemma rademacher_Y (a : ℝ) : μ {ω | Y ω = a} =
    if a = -1 ∨ a = 1 then (1/2 : ℝ≥0∞) else 0 := by
  classical
  simp only [mass, Fintype.sum_prod_type, Fin.sum_univ_two, Set.mem_setOf_eq,
    Y, sign, Matrix.cons_val_zero, Matrix.cons_val_one]
  by_cases h₁ : a = -1 <;> by_cases h₂ : a = 1 <;> (norm_num [h₁, h₂, eq_comm] <;> apply (ENNReal.toReal_eq_toReal (by simp [div_eq_mul_inv, ENNReal.mul_ne_top]) (by simp [div_eq_mul_inv, ENNReal.mul_ne_top])).mp <;> norm_num [ENNReal.toReal_add, div_eq_mul_inv])
def A : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; -1, 0]
def z (ω : Ω) : Fin 2 → ℝ := ![X ω, Y ω]
def quadratic (B : Matrix (Fin 2) (Fin 2) ℝ) (v : Fin 2 → ℝ) : ℝ :=
  ∑ i, ∑ j, v i * B i j * v j
def estimator : Ω → ℝ := fun ω => quadratic A (z ω)
lemma quadratic_zero (v : Fin 2 → ℝ) : quadratic A v = 0 := by
  simp [quadratic, A, Fin.sum_univ_two]; ring
lemma estimator_zero : estimator = 0 := by
  funext ω; exact quadratic_zero (z ω)
lemma unbiased : (∫ ω, estimator ω ∂μ) = Matrix.trace A := by
  rw [estimator_zero]; simp [Matrix.trace, A, Fin.sum_univ_two]
lemma actual_variance : variance estimator μ = 0 := by rw [estimator_zero, variance_zero]
def frobeniusSquared (B : Matrix (Fin 2) (Fin 2) ℝ) : ℝ := ∑ i, ∑ j, (B i j)^2
def frobeniusNorm (B : Matrix (Fin 2) (Fin 2) ℝ) : ℝ := Real.sqrt (frobeniusSquared B)
def diagonalSquared (B : Matrix (Fin 2) (Fin 2) ℝ) : ℝ := ∑ i, (B i i)^2
lemma frobenius_squared : frobeniusNorm A ^ 2 = 2 := by
  norm_num [frobeniusNorm, frobeniusSquared, A, Fin.sum_univ_two]
lemma diagonal_squared : diagonalSquared A = 0 := by
  norm_num [diagonalSquared, A, Fin.sum_univ_two]
theorem variance_formula_false : variance estimator μ ≠
    2 * (frobeniusNorm A ^ 2 - diagonalSquared A) := by
  rw [actual_variance, frobenius_squared, diagonal_squared]; norm_num
#print axioms independent
#print axioms rademacher_X
#print axioms rademacher_Y
#print axioms unbiased
#print axioms actual_variance
#print axioms frobenius_squared
#print axioms variance_formula_false
end HutchinsonCounterexample
