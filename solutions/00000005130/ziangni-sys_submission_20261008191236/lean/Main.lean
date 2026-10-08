import Mathlib.Algebra.Algebra.Spectrum.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Real.StarOrdered
import Mathlib.Tactic

noncomputable section
open scoped Matrix
namespace RotatedPreconditioners
abbrev M := Matrix (Fin 2) (Fin 2) ℝ
abbrev V := Fin 2 → ℝ

def M1 : M := Matrix.diagonal ![1,2]
def M2 : M := Matrix.diagonal ![2,1]
def R : M := !![0,-1;1,0]
def b : V := ![1,0]
def step (B : M) : M := 1-B⁻¹
/-- The actual preconditioned Richardson error recurrence for A = I. -/
def error (B : M) (v : V) : ℕ → V
  | 0 => v
  | n+1 => step B *ᵥ error B v n
def iterate (B : M) (rhs : V) (n : ℕ) : V := rhs-error B rhs n
def euclideanNorm (v : V) : ℝ := Real.sqrt ((v 0)^2+(v 1)^2)

theorem positive_definite : M1.PosDef ∧ M2.PosDef := by
  constructor <;> apply Matrix.PosDef.diagonal <;> intro i <;> fin_cases i <;> norm_num

theorem inverse_one : M1⁻¹=Matrix.diagonal ![1,(1:ℝ)/2] := by
  apply Matrix.inv_eq_left_inv
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [M1,Matrix.mul_apply,Fin.sum_univ_two]
theorem inverse_two : M2⁻¹=Matrix.diagonal ![(1:ℝ)/2,1] := by
  apply Matrix.inv_eq_left_inv
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [M2,Matrix.mul_apply,Fin.sum_univ_two]

theorem diagonal_spectrum (a c : ℝ) :
    spectrum ℝ (Matrix.diagonal ![a,c] : M)={a,c} := by
  ext z
  simp [spectrum.mem_iff,Matrix.isUnit_iff_isUnit_det,Matrix.det_fin_two,
    Matrix.algebraMap_eq_diagonal,isUnit_iff_ne_zero,mul_eq_zero,sub_eq_zero]
  tauto

theorem same_preconditioner_spectrum : spectrum ℝ M1=spectrum ℝ M2 := by
  simp only [M1,M2,diagonal_spectrum]
  ext z; simp; tauto

theorem same_preconditioned_spectrum :
    spectrum ℝ (M1⁻¹*1)={(1:ℝ),1/2} ∧ spectrum ℝ (M2⁻¹*1)={(1:ℝ),1/2} := by
  rw [mul_one,mul_one,inverse_one,inverse_two,diagonal_spectrum,diagonal_spectrum]
  constructor
  · rfl
  · ext z; simp; tauto

theorem quarter_turn : Rᵀ*R=1 ∧ R*Rᵀ=1 ∧ R.det=1 := by
  constructor
  · ext i j; fin_cases i <;> fin_cases j <;> norm_num [R,Matrix.mul_apply,Fin.sum_univ_two]
  constructor
  · ext i j; fin_cases i <;> fin_cases j <;> norm_num [R,Matrix.mul_apply,Fin.sum_univ_two]
  · norm_num [R,Matrix.det_fin_two]

theorem rotation_preconditioner : M2=R*M1*Rᵀ := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [R,M1,M2,Matrix.mul_apply,Matrix.vecMul,Matrix.mulVec, dotProduct,Fin.sum_univ_two]

theorem step_one : step M1=Matrix.diagonal ![0,(1:ℝ)/2] := by
  rw [step,inverse_one]
  ext i j; fin_cases i <;> fin_cases j <;> norm_num
theorem step_two : step M2=Matrix.diagonal ![(1:ℝ)/2,0] := by
  rw [step,inverse_two]
  ext i j; fin_cases i <;> fin_cases j <;> norm_num

theorem identical_iteration_spectra :
    spectrum ℝ (step M1)={(0:ℝ),1/2} ∧ spectrum ℝ (step M2)={(0:ℝ),1/2} := by
  rw [step_one,step_two,diagonal_spectrum,diagonal_spectrum]
  constructor
  · rfl
  · ext z; simp; tauto

theorem richardson_recurrence (B : M) (rhs : V) (n : ℕ) :
    iterate B rhs (n+1)=iterate B rhs n+B⁻¹ *ᵥ (rhs-iterate B rhs n) := by
  simp only [iterate,error,step,Matrix.sub_mulVec,Matrix.one_mulVec,sub_sub_cancel]
  abel

theorem initial_iterate (B : M) (rhs : V) : iterate B rhs 0=0 := by simp [iterate,error]
theorem unit_initial : euclideanNorm b=1 := by norm_num [euclideanNorm,b]

theorem first_terminates (n : ℕ) : error M1 b (n+1)=0 := by
  induction n with
  | zero =>
    rw [error,error,step_one]
    ext i; fin_cases i <;> simp [b,Matrix.mulVec_diagonal]
  | succ n ih => rw [error,ih,Matrix.mulVec_zero]

theorem second_errors (n : ℕ) : error M2 b n=((1:ℝ)/2)^n • b := by
  induction n with
  | zero => simp [error]
  | succ n ih =>
    rw [error,ih,step_two]
    ext i
    fin_cases i <;> simp [Matrix.mulVec_diagonal,b,pow_succ] <;> ring

theorem error_norms (n : ℕ) : euclideanNorm (error M1 b (n+1))=0 ∧
    euclideanNorm (error M2 b n)=((1:ℝ)/2)^n := by
  rw [first_terminates,second_errors]
  constructor
  · simp [euclideanNorm]
  · simp [euclideanNorm,b,Real.sqrt_sq_eq_abs,abs_of_nonneg (pow_nonneg (by norm_num) n)]

theorem trajectories_differ : iterate M1 b 1≠iterate M2 b 1 := by
  intro h
  have he := congrFun h 0
  norm_num [iterate,error,step_one,step_two,b,Matrix.mulVec_diagonal] at he

theorem intertwining : step M2*R=R*step M1 := by
  rw [step_one,step_two]
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [R,Matrix.mul_apply,Fin.sum_univ_two]

theorem rotation_trajectory (v : V) (n : ℕ) :
    error M2 (R *ᵥ v) n=R *ᵥ error M1 v n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [error,ih,Matrix.mulVec_mulVec,intertwining]

theorem initial_direction_rotation (n : ℕ) :
    error M2 b n=R *ᵥ error M1 (Rᵀ *ᵥ b) n := by
  have h := rotation_trajectory (Rᵀ *ᵥ b) n
  simpa only [Matrix.mulVec_mulVec,quarter_turn.2.1,Matrix.one_mulVec] using h

theorem existence_claim : ∃ B C : M,
    B.PosDef ∧ C.PosDef ∧ spectrum ℝ B=spectrum ℝ C ∧
    spectrum ℝ (B⁻¹*1)=spectrum ℝ (C⁻¹*1) ∧ iterate B b 1≠iterate C b 1 := by
  exact ⟨M1,M2,positive_definite.1,positive_definite.2,same_preconditioner_spectrum,
    same_preconditioned_spectrum.1.trans same_preconditioned_spectrum.2.symm,trajectories_differ⟩

#print axioms positive_definite
#print axioms inverse_one
#print axioms inverse_two
#print axioms same_preconditioner_spectrum
#print axioms same_preconditioned_spectrum
#print axioms quarter_turn
#print axioms rotation_preconditioner
#print axioms identical_iteration_spectra
#print axioms richardson_recurrence
#print axioms unit_initial
#print axioms first_terminates
#print axioms second_errors
#print axioms error_norms
#print axioms trajectories_differ
#print axioms initial_direction_rotation
#print axioms existence_claim
end RotatedPreconditioners
