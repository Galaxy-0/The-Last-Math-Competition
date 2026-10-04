import Mathlib.Data.Matrix.ConjTranspose
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

namespace SchattenCounterexample
noncomputable section
open scoped Matrix
abbrev OneMatrix := Matrix (Fin 1) (Fin 1) ℂ

def Gram (M : OneMatrix) : OneMatrix := M.conjTranspose * M
def IsEigenvalue (M : OneMatrix) (z : ℂ) : Prop :=
  ∃ v : Fin 1 → ℂ, v ≠ 0 ∧ M.mulVec v = z • v

theorem eigenvalue_iff (M : OneMatrix) (z : ℂ) : IsEigenvalue M z ↔ z = M 0 0 := by
  constructor
  · rintro ⟨v,hv,he⟩
    have hv0 : v 0 ≠ 0 := by
      intro h
      apply hv
      funext i
      have hi : i = 0 := Subsingleton.elim _ _
      simpa [hi] using h
    have he0 := congrFun he 0
    have heq : M 0 0 * v 0 = z * v 0 := by
      simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_one, smul_eq_mul] using he0
    exact (mul_right_cancel₀ hv0 heq).symm
  · intro hz
    refine ⟨fun _ => 1, ?_, ?_⟩
    · intro h
      have h0 := congrFun h 0
      norm_num at h0
    · funext i
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_one, smul_eq_mul, hz]

theorem gram_entry (M : OneMatrix) : Gram M 0 0 = (Complex.normSq (M 0 0) : ℂ) := by
  simp [Gram, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_one,
    Complex.star_def, ← Complex.normSq_eq_conj_mul_self]

-- The single singular value is the nonnegative square root of the sole Gram eigenvalue.
def singularValues (M : OneMatrix) : Fin 1 → ℝ := fun _ => Real.sqrt ((Gram M 0 0).re)

theorem singular_value_correct (M : OneMatrix) :
    0 ≤ singularValues M 0 ∧ ((singularValues M 0)^2 : ℂ) = Gram M 0 0 := by
  rw [gram_entry]
  simp only [singularValues, gram_entry, Complex.ofReal_re]
  constructor
  · exact Real.sqrt_nonneg _
  · norm_cast
    exact Real.sq_sqrt (Complex.normSq_nonneg _)

theorem gram_spectrum (M : OneMatrix) (z : ℂ) :
    IsEigenvalue (Gram M) z ↔ z = ((singularValues M 0)^2 : ℂ) := by
  rw [eigenvalue_iff, singular_value_correct M |>.2]

-- This is the standard finite-dimensional Schatten p formula, specialized to dimension one.
def schatten (M : OneMatrix) (p : ℝ) : ℝ :=
  (∑ i : Fin 1, (singularValues M i)^p)^(1/p)

theorem schatten_half (M : OneMatrix) : schatten M (1/2) = singularValues M 0 := by
  unfold schatten
  rw [Fin.sum_univ_one]
  rw [show (1/(1/2 : ℝ)) = 2 by norm_num, Real.rpow_two, ← Real.sqrt_eq_rpow]
  exact Real.sq_sqrt (singular_value_correct M).1

def identity : OneMatrix := 1

theorem witness_singular_values : singularValues identity 0 = 1 ∧
    singularValues (identity+identity) 0 = 2 := by
  simp only [singularValues, gram_entry, Matrix.add_apply, identity, Matrix.one_apply_eq, Complex.ofReal_re]
  norm_num [Complex.normSq_apply]
  rw [show (4 : ℝ) = (2 : ℝ)^2 by norm_num, Real.sqrt_sq_eq_abs]
  norm_num

theorem actual_schatten_values : schatten identity (1/2) = 1 ∧
    schatten (identity+identity) (1/2) = 2 := by
  simp only [schatten_half]
  exact witness_singular_values

def claimedConstant (p : ℝ) : ℝ := (2 : ℝ)^(1-1/p)

theorem claimed_constant_half : claimedConstant (1/2) = 1/2 := by
  unfold claimedConstant
  rw [show (1-1/(1/2 : ℝ)) = -1 by norm_num, Real.rpow_neg_one]
  norm_num

def TriangleBound (p c : ℝ) : Prop := ∀ M N : OneMatrix,
  schatten (M+N) p ≤ c * (schatten M p + schatten N p)

theorem witness_violation : claimedConstant (1/2) *
    (schatten identity (1/2)+schatten identity (1/2)) <
    schatten (identity+identity) (1/2) := by
  rw [claimed_constant_half, actual_schatten_values.1, actual_schatten_values.2]
  norm_num

theorem conjecture_00000008574_triangle_false : ¬ TriangleBound (1/2) (claimedConstant (1/2)) := by
  intro h
  exact not_le_of_gt witness_violation (h identity identity)

#print axioms eigenvalue_iff
#print axioms gram_entry
#print axioms singular_value_correct
#print axioms schatten_half
#print axioms actual_schatten_values
#print axioms conjecture_00000008574_triangle_false
end
end SchattenCounterexample
