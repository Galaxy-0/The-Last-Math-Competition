import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Complex.OperatorNorm
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Tactic

noncomputable section
namespace ConditionCounterexample
open scoped ComplexConjugate
open Matrix
abbrev Op := ℂ →L[ℝ] ℂ

def A : Op := (((2 * Complex.I : ℂ) • ContinuousLinearMap.id ℂ ℂ).restrictScalars ℝ)
def B : Op := (((-Complex.I / 2 : ℂ) • ContinuousLinearMap.id ℂ ℂ).restrictScalars ℝ)

theorem A_apply (z : ℂ) : A z = 2 * Complex.I * z := rfl
theorem B_apply (z : ℂ) : B z = (-Complex.I / 2) * z := rfl

theorem coordinates (z : ℂ) : (A z).re = -2 * z.im ∧ (A z).im = 2 * z.re := by
  simp [A_apply, Complex.mul_re, Complex.mul_im]

theorem inverse_left : B * A = 1 := by
  ext z
  simp only [ContinuousLinearMap.mul_apply, B_apply, A_apply, ContinuousLinearMap.one_apply]
  calc
    (-Complex.I / 2) * (2 * Complex.I * z) = -(Complex.I * Complex.I) * z := by ring
    _ = z := by simp

theorem inverse_right : A * B = 1 := by
  ext z
  simp only [ContinuousLinearMap.mul_apply, B_apply, A_apply, ContinuousLinearMap.one_apply]
  calc
    (2 * Complex.I) * ((-Complex.I / 2) * z) = -(Complex.I * Complex.I) * z := by ring
    _ = z := by simp

theorem norm_A : ‖A‖ = 2 := by
  rw [A, ContinuousLinearMap.norm_restrictScalars]
  simp [norm_smul, norm_mul]

theorem norm_B : ‖B‖ = 1 / 2 := by
  rw [B, ContinuousLinearMap.norm_restrictScalars]
  simp [norm_smul, norm_div]

theorem adjoint_A : ContinuousLinearMap.adjoint A = -A := by
  apply Eq.symm
  apply (ContinuousLinearMap.eq_adjoint_iff (-A) A).mpr
  intro x y
  simp only [ContinuousLinearMap.neg_apply, A_apply, Complex.inner]
  simp [Complex.mul_re, Complex.mul_im]
  ring

def antisymmetric : Op := (1 / 2 : ℝ) • (A - ContinuousLinearMap.adjoint A)
def condition : ℝ := ‖A‖ * ‖B‖

theorem antisymmetric_eq : antisymmetric = A := by
  rw [antisymmetric, adjoint_A]
  ext z
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.neg_apply]
  module

theorem normal : star A * A = A * star A := by
  rw [ContinuousLinearMap.star_eq_adjoint, adjoint_A]
  ext z
  simp [ContinuousLinearMap.mul_apply]

theorem norm_antisymmetric : ‖antisymmetric‖ = 2 := by rw [antisymmetric_eq, norm_A]
theorem condition_one : condition = 1 := by norm_num [condition, norm_A, norm_B]

theorem lower_bound_false : ¬ ‖antisymmetric‖ ≤ condition := by
  norm_num [norm_antisymmetric, condition_one]

def realMatrix : Matrix (Fin 2) (Fin 2) ℝ := !![0, -2; 2, 0]

theorem coordinate_matrix (z : ℂ) :
    realMatrix *ᵥ ![z.re, z.im] = ![(A z).re, (A z).im] := by
  ext i
  fin_cases i <;> simp [realMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two, coordinates z]

def complexMatrix : Matrix (Fin 2) (Fin 2) ℂ := !![0, -2; 2, 0]

theorem characteristic_determinant (z : ℂ) :
    (complexMatrix - z • (1 : Matrix (Fin 2) (Fin 2) ℂ)).det =
      (z - 2 * Complex.I) * (z + 2 * Complex.I) := by
  simp [complexMatrix, Matrix.det_fin_two, Matrix.smul_apply, Matrix.one_apply]
  ring_nf
  simp [Complex.I_sq]
  ring

theorem eigenvalues (z : ℂ) :
    (complexMatrix - z • (1 : Matrix (Fin 2) (Fin 2) ℂ)).det = 0 ↔
      z = 2 * Complex.I ∨ z = -2 * Complex.I := by
  rw [characteristic_determinant, mul_eq_zero]
  constructor
  · rintro (h | h)
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (by simpa [neg_mul] using eq_neg_of_add_eq_zero_left h)
  · rintro (rfl | rfl) <;> simp

theorem eigenvalue_moduli : ‖(2 * Complex.I : ℂ)‖ = 2 ∧ ‖(-2 * Complex.I : ℂ)‖ = 2 := by
  norm_num [norm_mul]

theorem spectral_ratio : ‖(2 * Complex.I : ℂ)‖ / ‖(-2 * Complex.I : ℂ)‖ = 1 := by
  rw [eigenvalue_moduli.1, eigenvalue_moduli.2]
  norm_num

theorem counterexample : B * A = 1 ∧ A * B = 1 ∧ (star A * A = A * star A) ∧
    condition = 1 ∧ ‖antisymmetric‖ = 2 ∧ ¬ ‖antisymmetric‖ ≤ condition :=
  ⟨inverse_left, inverse_right, normal, condition_one, norm_antisymmetric, lower_bound_false⟩
end ConditionCounterexample
end
#print axioms ConditionCounterexample.inverse_left
#print axioms ConditionCounterexample.adjoint_A
#print axioms ConditionCounterexample.norm_A
#print axioms ConditionCounterexample.norm_B
#print axioms ConditionCounterexample.eigenvalues
#print axioms ConditionCounterexample.counterexample
