import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
Counterexample to the first assertion of conjecture 00000007755.
All coefficients lie in an algebraic closure of Q, and critical points are
tested in that algebraic closure rather than only among rational points.
-/

namespace TLMC7755

abbrev K := AlgebraicClosure ℚ

noncomputable def f (a : K) : Polynomial K :=
  (Polynomial.X - Polynomial.C a) ^ 2 + Polynomial.C a

def Preperiodic (p : Polynomial K) (x : K) : Prop :=
  ∃ m n : ℕ, m < n ∧ (p.eval^[m]) x = (p.eval^[n]) x

def PCF (p : Polynomial K) : Prop :=
  ∀ x : K, p.derivative.eval x = 0 → Preperiodic p x

theorem eval_f_self (a : K) : (f a).eval a = a := by
  simp [f]

theorem derivative_f (a : K) : (f a).derivative = 2 * (Polynomial.X - Polynomial.C a) := by
  simp [f, pow_two, Polynomial.derivative_mul]
  ring

theorem critical_iff (a x : K) : (f a).derivative.eval x = 0 ↔ x = a := by
  rw [derivative_f]
  simp [sub_eq_zero]

theorem pcf_f (a : K) : PCF (f a) := by
  intro x hx
  have hxa : x = a := (critical_iff a x).mp hx
  subst x
  refine ⟨0, 1, by decide, ?_⟩
  simp [eval_f_self]

theorem degree_f (a : K) : (f a).degree = 2 := by
  have hd : ((Polynomial.X - Polynomial.C a) ^ 2).degree = 2 := by
    simp [Polynomial.degree_pow, Polynomial.degree_X_sub_C]
  unfold f
  rw [Polynomial.degree_add_C (by rw [hd]; decide)]
  exact hd

theorem f_injective : Function.Injective f := by
  intro a b hab
  have h : (f a).derivative = (f b).derivative := congrArg Polynomial.derivative hab
  have ha : (f a).derivative.eval a = 0 := (critical_iff a a).mpr rfl
  rw [h] at ha
  exact (critical_iff b a).mp ha

theorem infinite_quadratic_pcf : Set.Infinite {p : Polynomial K | p.degree = 2 ∧ PCF p} := by
  have hi : Set.Infinite (Set.range f) := Set.infinite_range_of_injective f_injective
  exact hi.mono (by
    rintro p ⟨a, rfl⟩
    exact ⟨degree_f a, pcf_f a⟩)

#print axioms infinite_quadratic_pcf

end TLMC7755
