import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace PencilCounterexample

open Matrix

abbrev Vec := Fin 2 → ℝ
abbrev Mat := Matrix (Fin 2) (Fin 2) ℝ

def A : Mat := !![1, 0; 0, 2]
def B : Mat := !![2, 1; 1, 3]
def witness : Vec := ![1, -1]

def Eigenvalue (M : Mat) (lambda : ℝ) : Prop :=
  ∃ v : Vec, v ≠ 0 ∧ M *ᵥ v = lambda • v

def GeneralizedEigenvalue (M N : Mat) (lambda : ℝ) : Prop :=
  ∃ v : Vec, v ≠ 0 ∧ M *ᵥ v = lambda • (N *ᵥ v)

def PositiveDefinite (M : Mat) : Prop :=
  ∀ v : Vec, v ≠ 0 → 0 < dotProduct v (M *ᵥ v)

theorem A_symmetric : A.transpose = A := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [A, transpose]

theorem B_symmetric : B.transpose = B := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [B, transpose]

theorem coordinates_not_both_zero {v : Vec} (hv : v ≠ 0) (hx : v 0 = 0) :
    v 1 ≠ 0 := by
  intro hy
  apply hv
  ext i
  fin_cases i <;> simp [hx, hy]

theorem A_positive : PositiveDefinite A := by
  intro v hv
  simp [dotProduct, mulVec, A, Fin.sum_univ_succ]
  by_cases hx : v 0 = 0
  · have hy := coordinates_not_both_zero hv hx
    nlinarith [sq_pos_of_ne_zero hy, sq_nonneg (v 0)]
  · nlinarith [sq_pos_of_ne_zero hx, sq_nonneg (v 1)]

theorem B_positive : PositiveDefinite B := by
  intro v hv
  simp [dotProduct, mulVec, B, Fin.sum_univ_succ]
  by_cases hx : v 0 = 0
  · have hy := coordinates_not_both_zero hv hx
    nlinarith [sq_pos_of_ne_zero hy, sq_nonneg (v 0), sq_nonneg (v 0 + v 1)]
  · nlinarith [sq_pos_of_ne_zero hx, sq_nonneg (v 1), sq_nonneg (v 0 + v 1)]

theorem witness_nonzero : witness ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  norm_num [witness] at h0

theorem pencil_eigenvalue_one : GeneralizedEigenvalue A B 1 := by
  refine ⟨witness, witness_nonzero, ?_⟩
  ext i
  fin_cases i <;> norm_num [A, B, witness, mulVec, dotProduct, Fin.sum_univ_succ]

theorem A_spectrum_subset {lambda : ℝ} (hlambda : Eigenvalue A lambda) :
    lambda = 1 ∨ lambda = 2 := by
  obtain ⟨v, hv0, hv⟩ := hlambda
  have h0 := congrFun hv 0
  have h1 := congrFun hv 1
  norm_num [A, mulVec, dotProduct, Fin.sum_univ_succ, Pi.smul_apply, smul_eq_mul] at h0 h1
  by_cases hl1 : lambda = 1
  · exact Or.inl hl1
  by_cases hl2 : lambda = 2
  · exact Or.inr hl2
  have hp0 : (lambda - 1) * v 0 = 0 := by nlinarith [h0]
  have hz0 := (mul_eq_zero.mp hp0).resolve_left (sub_ne_zero.mpr hl1)
  have hz1 := h1.resolve_left (Ne.symm hl2)
  exfalso
  apply hv0
  ext i
  fin_cases i <;> simp [hz0, hz1]

theorem A_spectrum_iff (lambda : ℝ) : Eigenvalue A lambda ↔ lambda = 1 ∨ lambda = 2 := by
  constructor
  · exact A_spectrum_subset
  · rintro (rfl | rfl)
    · refine ⟨![1, 0], ?_, ?_⟩
      · intro h
        have h0 := congrFun h 0
        norm_num at h0
      · ext i
        fin_cases i <;> norm_num [A, mulVec, dotProduct, Fin.sum_univ_succ]
    · refine ⟨![0, 1], ?_, ?_⟩
      · intro h
        have h1 := congrFun h 1
        norm_num at h1
      · ext i
        fin_cases i <;> norm_num [A, mulVec, dotProduct, Fin.sum_univ_succ]

theorem B_not_one : ¬ Eigenvalue B 1 := by
  rintro ⟨v, hv0, hv⟩
  have h0 := congrFun hv 0
  have h1 := congrFun hv 1
  norm_num [B, mulVec, dotProduct, Fin.sum_univ_succ, Pi.smul_apply, smul_eq_mul] at h0 h1
  have hz0 : v 0 = 0 := by linarith
  have hz1 : v 1 = 0 := by linarith
  apply hv0
  ext i
  fin_cases i <;> simp [hz0, hz1]

theorem B_not_two : ¬ Eigenvalue B 2 := by
  rintro ⟨v, hv0, hv⟩
  have h0 := congrFun hv 0
  have h1 := congrFun hv 1
  norm_num [B, mulVec, dotProduct, Fin.sum_univ_succ, Pi.smul_apply, smul_eq_mul] at h0 h1
  have hz0 : v 0 = 0 := by linarith
  have hz1 : v 1 = 0 := by linarith
  apply hv0
  ext i
  fin_cases i <;> simp [hz0, hz1]

theorem no_individual_spectral_quotient :
    ¬ (∃ alpha beta : ℝ, Eigenvalue A alpha ∧ Eigenvalue B beta ∧
      beta ≠ 0 ∧ (1 : ℝ) = alpha / beta) := by
  rintro ⟨alpha, beta, ha, hb, hb0, hratio⟩
  have heq : alpha = beta := by
    have h : (1 : ℝ) * beta = alpha := (eq_div_iff hb0).mp hratio
    simpa using h.symm
  subst beta
  rcases A_spectrum_subset ha with h1 | h2
  · subst alpha
    exact B_not_one hb
  · subst alpha
    exact B_not_two hb

theorem conjecture_7177_counterexample :
    A.transpose = A ∧ B.transpose = B ∧ PositiveDefinite A ∧ PositiveDefinite B ∧
    GeneralizedEigenvalue A B 1 ∧
    ¬ (∃ alpha beta : ℝ, Eigenvalue A alpha ∧ Eigenvalue B beta ∧
      beta ≠ 0 ∧ (1 : ℝ) = alpha / beta) :=
  ⟨A_symmetric, B_symmetric, A_positive, B_positive, pencil_eigenvalue_one,
    no_individual_spectral_quotient⟩

end PencilCounterexample

#print axioms PencilCounterexample.A_positive
#print axioms PencilCounterexample.B_positive
#print axioms PencilCounterexample.pencil_eigenvalue_one
#print axioms PencilCounterexample.A_spectrum_subset
#print axioms PencilCounterexample.A_spectrum_iff
#print axioms PencilCounterexample.no_individual_spectral_quotient
#print axioms PencilCounterexample.conjecture_7177_counterexample
