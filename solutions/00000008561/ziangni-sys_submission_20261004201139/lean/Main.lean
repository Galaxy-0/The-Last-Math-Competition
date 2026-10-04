import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option maxHeartbeats 400000
noncomputable section
namespace PseudospectralArea
open Matrix MeasureTheory
abbrev H := EuclideanSpace ℂ (Fin 2)
abbrev Mat := Matrix (Fin 2) (Fin 2) ℂ
abbrev Op := H →L[ℂ] H

def linearRep : Mat ≃⋆ₐ[ℂ] (H →ₗ[ℂ] H) :=
  (LinearMap.toMatrixOrthonormal (EuclideanSpace.basisFun (Fin 2) ℂ)).symm

def rep : Mat ≃ₐ[ℂ] Op :=
  (linearRep : Mat ≃ₐ[ℂ] (H →ₗ[ℂ] H)).trans (Module.End.toContinuousLinearMap (𝕜 := ℂ) H)

theorem rep_apply (A : Mat) (x : H) (i : Fin 2) :
    rep A x i = ∑ j, A i j * x j := by rfl

theorem rep_star (A : Mat) : rep (star A) = star (rep A) := by
  change LinearMap.toContinuousLinearMap (linearRep (star A)) = _
  rw [map_star]
  rfl

def A : Mat := !![1, 3; 0, -1]
def D : Mat := !![1, 0; 0, -1]
def N : Mat := !![0, 1; 0, 0]
def V : Mat := !![1, -(3/2); 0, 1]
def W : Mat := !![1, 3/2; 0, 1]
def T : Op := rep A

theorem nonnormal : star T * T ≠ T * star T := by
  intro h
  have hm : star A * A = A * star A := rep.injective (by
    simpa only [map_mul, rep_star, T] using h)
  have h00 := congrArg (fun M : Mat => M 0 0) hm
  norm_num [A, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
    Matrix.mul_apply, Fin.sum_univ_two] at h00

theorem matrix_decomposition : A = D + (3 : ℂ) • N := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [A, D, N]

theorem norm_diagonal_apply (x : H) : ‖rep D x‖ = ‖x‖ := by
  simp only [EuclideanSpace.norm_eq, Fin.sum_univ_two]
  congr 1
  simp [rep_apply, D, Fin.sum_univ_two]

theorem diagonal_norm_le : ‖rep D‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  rw [norm_diagonal_apply, one_mul]

theorem norm_nilpotent_apply (x : H) : ‖rep N x‖ = ‖x 1‖ := by
  have h : rep N x = EuclideanSpace.single 0 (x 1) := by
    ext i; fin_cases i <;> simp [rep_apply, N, Fin.sum_univ_two, EuclideanSpace.single_apply]
  rw [h, EuclideanSpace.norm_single]

theorem nilpotent_norm_le : ‖rep N‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  rw [norm_nilpotent_apply, one_mul]
  exact PiLp.norm_apply_le x 1

theorem operator_norm_upper : ‖T‖ ≤ 4 := by
  have hd : T = rep D + (3 : ℂ) • rep N := by
    rw [T, matrix_decomposition, map_add, map_smul]
  rw [hd]
  calc
    _ ≤ ‖rep D‖ + ‖(3 : ℂ) • rep N‖ := norm_add_le _ _
    _ = ‖rep D‖ + 3 * ‖rep N‖ := by
      congr 1
      calc
        ‖(3 : ℂ) • rep N‖ = ‖(3 : ℂ)‖ * ‖rep N‖ := norm_smul (3 : ℂ) (rep N)
        _ = 3 * ‖rep N‖ := by norm_num
    _ ≤ 4 := by nlinarith [diagonal_norm_le, nilpotent_norm_le]

def e1 : H := EuclideanSpace.single 1 1

theorem operator_norm_lower : 3 ≤ ‖T‖ := by
  have he : ‖e1‖ = 1 := by simp [e1, EuclideanSpace.norm_single]
  have hc : ‖(T e1) 0‖ = 3 := by
    norm_num [T, rep_apply, A, Fin.sum_univ_two, e1, EuclideanSpace.single_apply]
  have h := (PiLp.norm_apply_le (T e1) 0).trans (T.le_opNorm e1)
  rw [hc, he, mul_one] at h
  exact h

theorem diagonalizer_matrices : V * W = 1 ∧ W * V = 1 ∧ A = V * D * W := by
  constructor
  · ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [V, W, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]
  constructor
  · ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [V, W, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]
  · ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [A, V, D, W, Matrix.mul_apply, Fin.sum_univ_two]

/-- All genuine ordered eigenbasis maps and their two-sided inverses. -/
def EigenbasisPair (v w : Op) : Prop :=
  v * w = 1 ∧ w * v = 1 ∧ T = v * rep D * w

theorem explicit_eigenbasis : EigenbasisPair (rep V) (rep W) := by
  rcases diagonalizer_matrices with ⟨h1,h2,h3⟩
  constructor
  · rw [← map_mul, h1, map_one]
  constructor
  · rw [← map_mul, h2, map_one]
  · rw [T, h3, map_mul, map_mul]

theorem every_condition_lower (v w : Op) (h : EigenbasisPair v w) :
    3 ≤ ‖v‖ * ‖w‖ := by
  have hu : ‖T‖ ≤ ‖v‖ * ‖w‖ := by
    rw [h.2.2]
    calc
      _ ≤ (‖v‖ * ‖rep D‖) * ‖w‖ := (norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ ‖v‖ * ‖w‖ := by
        nlinarith [diagonal_norm_le, norm_nonneg v, norm_nonneg w,
          mul_le_mul_of_nonneg_left diagonal_norm_le (norm_nonneg v)]
  exact operator_norm_lower.trans hu

def conditions : Set ℝ := {c | ∃ v w, EigenbasisPair v w ∧ c = ‖v‖ * ‖w‖}
def kappa : ℝ := sInf conditions

theorem conditions_nonempty : conditions.Nonempty :=
  ⟨_, rep V, rep W, explicit_eigenbasis, rfl⟩

theorem kappa_lower : 3 ≤ kappa := by
  apply le_csInf conditions_nonempty
  rintro c ⟨v,w,h,rfl⟩
  exact every_condition_lower v w h

/-- The usual pseudospectrum, including the spectral points. -/
def pseudo : Set ℂ := spectrum ℂ T ∪
  {z | z ∈ resolventSet ℂ T ∧ (1 / 10 : ℝ) < ‖resolvent T z‖}

theorem resolvent_equation (z : ℂ) (hz : z ∈ resolventSet ℂ T) :
    z • resolvent T z = 1 + T * resolvent T z := by
  have h := Ring.mul_inverse_cancel (algebraMap ℂ Op z - T) hz
  change (algebraMap ℂ Op z - T) * resolvent T z = 1 at h
  rw [sub_mul, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul] at h
  exact sub_eq_iff_eq_add.mp h

theorem resolvent_bound (z : ℂ) (hz : 14 ≤ ‖z‖) :
    z ∈ resolventSet ℂ T ∧ ‖resolvent T z‖ ≤ (1 / 10 : ℝ) := by
  have hres : z ∈ resolventSet ℂ T :=
    spectrum.mem_resolventSet_of_norm_lt (lt_of_le_of_lt operator_norm_upper (by linarith))
  refine ⟨hres, ?_⟩
  have heq := resolvent_equation z hres
  have hnorm : ‖z‖ * ‖resolvent T z‖ ≤ 1 + 4 * ‖resolvent T z‖ := by
    calc
      _ = ‖z • resolvent T z‖ := (norm_smul z (resolvent T z)).symm
      _ = ‖1 + T * resolvent T z‖ := congrArg (fun q : Op => ‖q‖) heq
      _ ≤ ‖(1 : Op)‖ + ‖T * resolvent T z‖ := norm_add_le _ _
      _ ≤ 1 + ‖T‖ * ‖resolvent T z‖ := by
        simpa only [norm_one] using add_le_add_left (norm_mul_le T (resolvent T z)) 1
      _ ≤ 1 + 4 * ‖resolvent T z‖ := by
        gcongr
        exact operator_norm_upper
  have hp := mul_le_mul_of_nonneg_right hz (norm_nonneg (resolvent T z))
  linarith

theorem pseudospectrum_contained : pseudo ⊆ Metric.closedBall 0 14 := by
  intro z hz
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra h
  have ho : 14 ≤ ‖z‖ := le_of_lt (lt_of_not_ge h)
  rcases resolvent_bound z ho with ⟨hres,hbound⟩
  rcases hz with hs | hp
  · exact hs hres
  · exact (not_lt_of_ge hbound) hp.2

def area : ℝ := (volume pseudo).toReal

theorem area_upper : area ≤ 196 * Real.pi := by
  have hm : volume pseudo ≤ volume (Metric.closedBall (0 : ℂ) 14) := measure_mono pseudospectrum_contained
  have hf : volume (Metric.closedBall (0 : ℂ) 14) ≠ ⊤ := by
    norm_num [Complex.volume_closedBall, ENNReal.mul_eq_top]
  have ht := ENNReal.toReal_mono hf hm
  norm_num [area, Complex.volume_closedBall, ENNReal.toReal_mul, ENNReal.toReal_pow] at ht ⊢
  exact ht

theorem area_finite : volume pseudo ≠ ⊤ := by
  apply ne_top_of_le_ne_top _ (measure_mono pseudospectrum_contained)
  norm_num [Complex.volume_closedBall, ENNReal.mul_eq_top]

theorem claimed_area_bound_fails : area < Real.pi * (10 : ℝ)^2 * kappa^2 := by
  have hk := kappa_lower
  have hsq : 9 ≤ kappa^2 := by nlinarith
  have hp := Real.pi_pos
  have hh := mul_le_mul_of_nonneg_left hsq (le_of_lt hp)
  nlinarith [area_upper]

#print axioms nonnormal
#print axioms explicit_eigenbasis
#print axioms operator_norm_upper
#print axioms operator_norm_lower
#print axioms every_condition_lower
#print axioms kappa_lower
#print axioms resolvent_bound
#print axioms pseudospectrum_contained
#print axioms area_finite
#print axioms claimed_area_bound_fails
end PseudospectralArea
