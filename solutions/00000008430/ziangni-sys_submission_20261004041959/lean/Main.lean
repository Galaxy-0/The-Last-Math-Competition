import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open scoped LinearAlgebra.Projectivization
open Polynomial

namespace SchubertCount8430

noncomputable section

/-- The actual lines in three-space, hence chains 0 < L < k^3 of dimensions 0,1,3. -/
def Lines (k : Type*) [Field k] :=
  { L : Submodule k (Fin 3 → k) // Module.finrank k L = 1 }

/-- Counts the full Grassmannian Schubert variety, not one affine Schubert cell. -/
theorem count_lines (k : Type*) [Field k] [Finite k] :
    Nat.card (Lines k) = (Nat.card k)^2 + Nat.card k + 1 := by
  rw [show Nat.card (Lines k) = Nat.card (ℙ k (Fin 3 → k)) from
    Nat.card_congr (Projectivization.equivSubmodule k (Fin 3 → k)).symm]
  rw [Projectivization.card_of_finrank k (Fin 3 → k) (show Module.finrank k (Fin 3 → k) = 3 by simp)]
  simp [Finset.sum_range_succ]
  omega

def countPolynomial : Polynomial ℂ := X^2 + X + 1

theorem countPolynomial_monic : countPolynomial.Monic := by
  unfold countPolynomial
  rw [add_assoc]
  apply monic_X_pow_add
  rw [show (1 : Polynomial ℂ) = C 1 by simp, degree_X_add_C]
  norm_num

theorem polynomial_counts (k : Type*) [Field k] [Finite k] :
    countPolynomial.eval (Nat.card k : ℂ) = (Nat.card (Lines k) : ℂ) := by
  rw [count_lines]
  simp [countPolynomial]

/-- Infinitely many prime fields make the counting polynomial uniquely determined. -/
theorem counting_polynomial_unique (P : Polynomial ℂ)
    (hP : ∀ (k : Type) [Field k] [Finite k],
      P.eval (Nat.card k : ℂ) = (Nat.card (Lines k) : ℂ)) : P = countPolynomial := by
  apply Polynomial.eq_of_infinite_eval_eq
  have hi : Set.Infinite ((fun p : ℕ => (p : ℂ)) '' {p : ℕ | Nat.Prime p}) :=
    Nat.infinite_setOf_prime.image Nat.cast_injective.injOn
  apply hi.mono
  rintro z ⟨p, hp, rfl⟩
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  have h := (hP (ZMod p)).trans (polynomial_counts (ZMod p)).symm
  simpa using h

def zeta : ℂ := ⟨-1 / 2, Real.sqrt 3 / 2⟩

theorem zeta_isRoot : countPolynomial.IsRoot zeta := by
  have hs : (Real.sqrt 3)^2 = 3 := Real.sq_sqrt (by norm_num)
  unfold Polynomial.IsRoot countPolynomial
  simp only [eval_add, eval_pow, eval_X, eval_one]
  apply Complex.ext
  · simp [zeta, pow_two, Complex.mul_re]
    nlinarith
  · simp [zeta, pow_two, Complex.mul_im]
    ring

theorem zeta_not_integer : ¬ ∃ m : ℤ, zeta = (m : ℂ) := by
  rintro ⟨m, hm⟩
  have him := congrArg Complex.im hm
  have hs : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  simp [zeta] at him

theorem conjecture_00000008430 :
    (∀ (k : Type) [Field k] [Finite k],
      countPolynomial.eval (Nat.card k : ℂ) = (Nat.card (Lines k) : ℂ)) ∧
    ∃ z : ℂ, countPolynomial.IsRoot z ∧ ¬ ∃ m : ℤ, z = (m : ℂ) := by
  exact ⟨fun k _ _ => polynomial_counts k, zeta, zeta_isRoot, zeta_not_integer⟩

end

end SchubertCount8430

#print axioms SchubertCount8430.count_lines
#print axioms SchubertCount8430.counting_polynomial_unique
#print axioms SchubertCount8430.countPolynomial_monic
#print axioms SchubertCount8430.conjecture_00000008430
