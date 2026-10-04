import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

namespace MIsometryCounterexample
noncomputable section
open Finset Matrix
open scoped ComplexConjugate
abbrev Mat := Matrix (Fin 2) (Fin 2) ℂ
abbrev H := EuclideanSpace ℂ (Fin 2)

def J : Mat := !![1, 1; 0, 1]

def gram (m : ℕ) (A : Mat) : Mat :=
  ∑ j ∈ range (m + 1),
    (((-1 : ℂ) ^ (m - j)) * (Nat.choose m j : ℂ)) • ((A ^ j).conjTranspose * A ^ j)

def operatorGram (m : ℕ) (L : H →ₗ[ℂ] H) : H →ₗ[ℂ] H :=
  ∑ j ∈ range (m + 1),
    (((-1 : ℂ) ^ (m - j)) * (Nat.choose m j : ℂ)) • (star (L ^ j) * L ^ j)

def representation : Mat ≃⋆ₐ[ℂ] (H →ₗ[ℂ] H) :=
  (LinearMap.toMatrixOrthonormal (EuclideanSpace.basisFun (Fin 2) ℂ)).symm

theorem jordan_continuous : Continuous (representation J) :=
  (representation J).continuous_of_finiteDimensional

theorem representation_gram (m : ℕ) (A : Mat) :
    representation (gram m A) = operatorGram m (representation A) := by
  simp [gram, operatorGram, ← Matrix.star_eq_conjTranspose, map_star]

theorem jordan_pow (j : ℕ) : J ^ j = !![1, (j : ℂ); 0, 1] := by
  induction j with
  | zero => ext i k; fin_cases i <;> fin_cases k <;> simp [Matrix.one_apply]
  | succ j ih =>
    rw [pow_succ, ih]
    ext i k
    fin_cases i <;> fin_cases k <;>
      simp [J, Matrix.mul_apply, Fin.sum_univ_two, Nat.cast_add, Nat.cast_one, add_comm]

theorem gram_one : gram 1 J = !![0, 1; 1, 1] := by
  ext i k
  fin_cases i <;> fin_cases k <;>
    norm_num [gram, Finset.sum_range_succ, jordan_pow, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.conjTranspose_apply, map_ofNat]

theorem gram_two : gram 2 J = !![0, 0; 0, 2] := by
  ext i k
  fin_cases i <;> fin_cases k <;>
    norm_num [gram, Finset.sum_range_succ, jordan_pow, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.conjTranspose_apply, map_ofNat]

theorem gram_three : gram 3 J = 0 := by
  ext i k
  fin_cases i <;> fin_cases k <;>
    norm_num [gram, Finset.sum_range_succ, jordan_pow, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.conjTranspose_apply, map_ofNat]

theorem gram_one_nonzero : gram 1 J ≠ 0 := by
  intro h
  have hc := congrArg (fun A : Mat => A 0 1) h
  rw [gram_one] at hc
  norm_num at hc

theorem gram_two_nonzero : gram 2 J ≠ 0 := by
  intro h
  have hc := congrArg (fun A : Mat => A 1 1) h
  rw [gram_two] at hc
  norm_num at hc

def IsMIsometry (m : ℕ) (L : H →ₗ[ℂ] H) : Prop :=
  0 < m ∧ operatorGram m L = 0

theorem gram_operator_iff (m : ℕ) :
    operatorGram m (representation J) = 0 ↔ gram m J = 0 := by
  rw [← representation_gram]
  exact representation.injective.eq_iff' representation.map_zero

theorem jordan_is_three : IsMIsometry 3 (representation J) := by
  refine ⟨by norm_num, (gram_operator_iff 3).mpr gram_three⟩

theorem no_smaller_positive_order (m : ℕ) (hm : 0 < m) (hsmall : m < 3) :
    ¬ IsMIsometry m (representation J) := by
  intro h
  have hg := (gram_operator_iff m).mp h.2
  interval_cases m
  · exact gram_one_nonzero hg
  · exact gram_two_nonzero hg

theorem ambient_dimension : Module.finrank ℂ H = 2 := by simp [H]

theorem dimension_bound_fails :
    IsMIsometry 3 (representation J) ∧
    (∀ m, 0 < m → m < 3 → ¬ IsMIsometry m (representation J)) ∧
    Module.finrank ℂ H < 3 := by
  exact ⟨jordan_is_three, no_smaller_positive_order, by rw [ambient_dimension]; norm_num⟩

#print axioms jordan_continuous
#print axioms jordan_pow
#print axioms representation_gram
#print axioms gram_three
#print axioms no_smaller_positive_order
#print axioms ambient_dimension
#print axioms dimension_bound_fails
end
end MIsometryCounterexample
