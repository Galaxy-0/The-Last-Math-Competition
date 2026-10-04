import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Data.Complex.ExponentialBounds
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Tactic

namespace RealBezoutCounterexample
noncomputable section
open MvPolynomial
abbrev Point := Fin 2 → ℝ

def equation (i : Fin 2) : MvPolynomial (Fin 2) ℝ := X i ^ 2 - C 1

def IsSolution (x : Point) : Prop := ∀ i, MvPolynomial.eval x (equation i) = 0

theorem equation_eval (i : Fin 2) (x : Point) :
    MvPolynomial.eval x (equation i) = x i ^ 2 - 1 := by
  simp [equation]

theorem equation_degree (i : Fin 2) : (equation i).totalDegree = 2 := by
  unfold equation
  rw [sub_eq_add_neg, totalDegree_add_eq_left_of_totalDegree_lt]
  · simp
  · simp

theorem solution_iff (x : Point) : IsSolution x ↔ ∀ i, x i = -1 ∨ x i = 1 := by
  simp only [IsSolution, equation_eval]
  constructor
  · intro h i
    have hi := h i
    have hf : (x i - 1) * (x i + 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp hf with h1 | h2
    · right; linarith
    · left; linarith
  · intro h i
    rcases h i with hi | hi <;> rw [hi] <;> norm_num

def sign (b : Bool) : ℝ := if b then 1 else -1

def rootEquiv : (Fin 2 → Bool) ≃ {x : Point // IsSolution x} where
  toFun b := ⟨fun i => sign (b i), (solution_iff _).mpr (by
    intro i; cases b i <;> simp [sign])⟩
  invFun x := fun i => decide (x.val i = 1)
  left_inv b := by
    funext i
    cases hb : b i <;> norm_num [sign, hb]
  right_inv x := by
    apply Subtype.ext
    funext i
    rcases (solution_iff x.val).mp x.property i with hi | hi <;> norm_num [sign, hi]

instance solutionFintype : Fintype {x : Point // IsSolution x} :=
  Fintype.ofEquiv (Fin 2 → Bool) rootEquiv

theorem solution_count : Fintype.card {x : Point // IsSolution x} = 4 := by
  rw [← Fintype.card_congr rootEquiv]
  norm_num

-- This explicit separation establishes that every counted root is isolated.
theorem roots_isolated (x y : {x : Point // IsSolution x})
    (h : dist x.val y.val < 1) : x = y := by
  apply Subtype.ext
  funext i
  have hc : |x.val i - y.val i| < 1 := by
    have hp := norm_le_pi_norm (x.val - y.val) i
    simp only [Pi.sub_apply, Real.norm_eq_abs] at hp
    rw [dist_eq_norm] at h
    exact lt_of_le_of_lt hp h
  rcases (solution_iff x.val).mp x.property i with hx | hx <;>
    rcases (solution_iff y.val).mp y.property i with hy | hy <;>
    rw [hx, hy] at hc ⊢ <;> norm_num at hc ⊢

def proposedBound (d m : ℕ) : ℝ := ((d : ℝ) / Real.sqrt m) ^ m * Real.exp (1 / 2)

theorem exp_half_lt_two : Real.exp (1 / 2) < 2 := by
  have he : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by
    rw [pow_two, ← Real.exp_add]
    norm_num
  have hb := Real.exp_one_lt_d9
  have hp := Real.exp_pos (1 / 2)
  nlinarith

theorem bound_at_two : proposedBound 2 2 = 2 * Real.exp (1 / 2) := by
  unfold proposedBound
  have hs : Real.sqrt 2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  norm_num only [Nat.cast_ofNat]
  rw [div_pow, hs]
  norm_num

theorem claimed_bound_fails :
    proposedBound 2 2 < (Fintype.card {x : Point // IsSolution x} : ℝ) := by
  rw [bound_at_two, solution_count]
  have h := exp_half_lt_two
  norm_num at *
  linarith

#print axioms equation_degree
#print axioms solution_count
#print axioms roots_isolated
#print axioms claimed_bound_fails
end
end RealBezoutCounterexample
