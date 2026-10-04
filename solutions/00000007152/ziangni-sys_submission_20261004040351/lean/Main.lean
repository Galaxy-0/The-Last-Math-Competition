import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace WeylEqualityCounterexample

open Matrix

abbrev Vec := Fin 3 → ℝ
abbrev Mat := Matrix (Fin 3) (Fin 3) ℝ

def A : Mat := !![3, 0, 0; 0, 1, 0; 0, 0, 0]
def B : Mat := !![3, 0, 0; 0, 1, 1; 0, 1, 1]
def e : Vec := ![1, 0, 0]
def w : Vec := ![0, 0, 1]

def Eigenvalue (M : Mat) (lambda : ℝ) : Prop :=
  ∃ v : Vec, v ≠ 0 ∧ M *ᵥ v = lambda • v

def LargestEigenvalue (M : Mat) (lambda : ℝ) : Prop :=
  Eigenvalue M lambda ∧ ∀ mu, Eigenvalue M mu → mu ≤ lambda

def Q (M : Mat) (v : Vec) : ℝ := ∑ i, v i * (M *ᵥ v) i
def S (v : Vec) : ℝ := ∑ i, (v i)^2

theorem A_symmetric : A.transpose = A := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [A, Matrix.transpose]

theorem B_symmetric : B.transpose = B := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [B, Matrix.transpose]

theorem S_formula (v : Vec) : S v = (v 0)^2 + (v 1)^2 + (v 2)^2 := by
  simp [S, Fin.sum_univ_succ]
  ring

theorem S_positive {v : Vec} (hv : v ≠ 0) : 0 < S v := by
  rw [S_formula]
  by_contra hn
  have hz0 : v 0 = 0 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1), sq_nonneg (v 2)]
  have hz1 : v 1 = 0 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1), sq_nonneg (v 2)]
  have hz2 : v 2 = 0 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1), sq_nonneg (v 2)]
  apply hv
  ext i
  fin_cases i <;> simp [hz0, hz1, hz2]

theorem Q_eigen {M : Mat} {lambda : ℝ} {v : Vec}
    (hv : M *ᵥ v = lambda • v) : Q M v = lambda * S v := by
  unfold Q S
  rw [hv, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem A_bound (v : Vec) : Q A v ≤ 3 * S v := by
  simp [Q, S, A, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  nlinarith [sq_nonneg (v 1), sq_nonneg (v 2)]

theorem B_bound (v : Vec) : Q B v ≤ 3 * S v := by
  simp [Q, S, B, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  nlinarith [sq_nonneg (v 1), sq_nonneg (v 2), sq_nonneg (v 1 - v 2)]

theorem sum_bound (v : Vec) : Q (A + B) v ≤ 6 * S v := by
  simp [Q, S, A, B, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  nlinarith [sq_nonneg (v 1), sq_nonneg (v 2), sq_nonneg (v 1 - v 2)]

theorem largest_from_bound {M : Mat} {c : ℝ}
    (he : Eigenvalue M c) (hbound : ∀ v, Q M v ≤ c * S v) :
    LargestEigenvalue M c := by
  refine ⟨he, ?_⟩
  rintro mu ⟨v, hv0, hv⟩
  have h := hbound v
  rw [Q_eigen hv] at h
  exact (mul_le_mul_right (S_positive hv0)).mp h

theorem e_nonzero : e ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  norm_num [e] at h0

theorem A_largest : LargestEigenvalue A 3 := by
  apply largest_from_bound
  · refine ⟨e, e_nonzero, ?_⟩
    ext i
    fin_cases i <;> norm_num [A, e, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  · exact A_bound

theorem B_largest : LargestEigenvalue B 3 := by
  apply largest_from_bound
  · refine ⟨e, e_nonzero, ?_⟩
    ext i
    fin_cases i <;> norm_num [B, e, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  · exact B_bound

theorem sum_largest : LargestEigenvalue (A + B) 6 := by
  apply largest_from_bound
  · refine ⟨e, e_nonzero, ?_⟩
    ext i
    fin_cases i <;> norm_num [A, B, e, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  · exact sum_bound

-- Any simultaneous eigenbasis would make the associated linear maps commute.
theorem no_common_eigenbasis {ι : Type*} (b : Basis ι ℝ Vec)
    (alpha beta : ι → ℝ)
    (ha : ∀ i, A *ᵥ b i = alpha i • b i)
    (hb : ∀ i, B *ᵥ b i = beta i • b i) : False := by
  let LA : Vec →ₗ[ℝ] Vec := Matrix.toLin' A
  let LB : Vec →ₗ[ℝ] Vec := Matrix.toLin' B
  have ha' : ∀ i, LA (b i) = alpha i • b i := ha
  have hb' : ∀ i, LB (b i) = beta i • b i := hb
  have hc : LA.comp LB = LB.comp LA := by
    apply b.ext
    intro i
    simp only [LinearMap.comp_apply, hb', ha', map_smul, smul_smul]
    rw [mul_comm]
  have htest := congrArg (fun L : Vec →ₗ[ℝ] Vec => L w 1) hc
  norm_num [LA, LB, LinearMap.comp_apply, Matrix.toLin'_apply,
    A, B, w, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at htest

def CommonEigenbasis : Prop :=
  ∃ (b : Basis (Fin 3) ℝ Vec) (alpha beta : Fin 3 → ℝ),
    (∀ i, A *ᵥ b i = alpha i • b i) ∧ (∀ i, B *ᵥ b i = beta i • b i)

theorem no_common_basis : ¬ CommonEigenbasis := by
  rintro ⟨b, alpha, beta, ha, hb⟩
  exact no_common_eigenbasis b alpha beta ha hb

-- Equality in the top Weyl bound is the specific extremal equality being refuted.
theorem conjecture_7152_counterexample :
    A.transpose = A ∧ B.transpose = B ∧
    LargestEigenvalue A 3 ∧ LargestEigenvalue B 3 ∧
    LargestEigenvalue (A + B) (3 + 3) ∧ ¬ CommonEigenbasis := by
  exact ⟨A_symmetric, B_symmetric, A_largest, B_largest,
    by simpa only [show (3 : ℝ) + 3 = 6 by norm_num] using sum_largest,
    no_common_basis⟩

end WeylEqualityCounterexample

#print axioms WeylEqualityCounterexample.A_largest
#print axioms WeylEqualityCounterexample.B_largest
#print axioms WeylEqualityCounterexample.sum_largest
#print axioms WeylEqualityCounterexample.no_common_eigenbasis
#print axioms WeylEqualityCounterexample.conjecture_7152_counterexample
