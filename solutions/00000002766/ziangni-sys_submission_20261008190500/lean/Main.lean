import Mathlib.Data.Matrix.Rank
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Degree.Definitions
import Mathlib.Tactic

noncomputable section
open Polynomial Matrix
namespace RankZeroIdentity
abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℚ
def identityPolynomial : ℚ[X] := X

theorem rank_zero_matrix (n : ℕ) (A : Mat n) (h : A.rank ≤ 0) : A = 0 := by
  have hr : A.rank = 0 := Nat.eq_zero_of_le_zero h
  have hb : LinearMap.range A.mulVecLin = ⊥ := Submodule.finrank_eq_zero.mp hr
  have hl : A.mulVecLin = 0 := LinearMap.range_eq_bot.mp hb
  ext i j
  have he := congrArg (fun T : (Fin n → ℚ) →ₗ[ℚ] (Fin n → ℚ) =>
    T (Pi.single j 1) i) hl
  simpa using he

theorem rank_zero_iff (n : ℕ) (A : Mat n) : A.rank ≤ 0 ↔ A = 0 := by
  constructor
  · exact rank_zero_matrix n A
  · intro h
    simp [h]

theorem genuine_identity (n : ℕ) (A : Mat n) (h : A.rank ≤ 0) :
    Polynomial.eval₂ (algebraMap ℚ (Mat n)) A identityPolynomial = 0 := by
  rw [rank_zero_matrix n A h]
  simp [identityPolynomial]

theorem polynomial_nonzero : identityPolynomial ≠ 0 := by simp [identityPolynomial]
theorem degree_one : identityPolynomial.natDegree = 1 := by simp [identityPolynomial]

-- If the minimum identity degree were 2r+2, every nonzero identity
-- would have at least that degree. The actual identity X violates it.
theorem minimum_degree_claim_false : ¬ (∀ p : ℚ[X], p ≠ 0 →
    (∀ n (A : Mat n), A.rank ≤ 0 → Polynomial.eval₂ (algebraMap ℚ (Mat n)) A p = 0) →
    2*0+2 ≤ p.natDegree) := by
  intro h
  have he := h identityPolynomial polynomial_nonzero genuine_identity
  rw [degree_one] at he
  norm_num at he

#print axioms rank_zero_iff
#print axioms genuine_identity
#print axioms polynomial_nonzero
#print axioms degree_one
#print axioms minimum_degree_claim_false
end RankZeroIdentity
