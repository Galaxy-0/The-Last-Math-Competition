import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Tactic

namespace CoprimeOrbitCounterexample
open Polynomial
noncomputable section
variable {R : Type*} [CommRing R]

def f : R[X] := X ^ 2
def g : R[X] := X ^ 2 - 1

/-- Actual composition iterates, with the identity polynomial at time zero. -/
def orbit (p : R[X]) : ℕ → R[X]
  | 0 => X
  | n + 1 => p.comp (orbit p n)

theorem initial_coprime : IsCoprime (f : R[X]) g := by
  refine ⟨1, -1, ?_⟩
  dsimp [f, g]
  ring

theorem f_orbit (n : ℕ) : orbit (f : R[X]) n = X ^ (2 ^ n) := by
  induction n with
  | zero => simp [orbit]
  | succ n ih =>
    simp only [orbit, f, pow_comp, X_comp, ih]
    change (orbit (f : R[X]) n) ^ 2 = X ^ (2 ^ (n + 1))
    rw [ih, ← pow_mul, Nat.pow_succ]

theorem g_even_step (k : ℕ) : orbit (g : R[X]) (2 * (k + 1)) =
    (orbit g (2 * k)) ^ 2 * ((orbit g (2 * k)) ^ 2 - 2) := by
  have h : 2 * (k + 1) = (2 * k + 1) + 1 := by omega
  rw [h]
  simp only [orbit, g, sub_comp, pow_comp, X_comp, one_comp]
  ring

theorem common_factor (k : ℕ) : (X ^ (2 ^ k) : R[X]) ∣ orbit g (2 * k) := by
  induction k with
  | zero => simp [orbit]
  | succ k ih =>
    rw [g_even_step]
    have hp : (X ^ (2 ^ (k + 1)) : R[X]) = (X ^ (2 ^ k)) ^ 2 := by
      rw [Nat.pow_succ, pow_mul]
    rw [hp]
    exact (pow_dvd_pow_of_dvd ih 2).trans (dvd_mul_right _ _)

theorem fixed_degrees : (f : ℚ[X]).natDegree = 2 ∧ (g : ℚ[X]).natDegree = 2 := by
  constructor
  · simp [f]
  · unfold g
    compute_degree; norm_num

theorem polynomial_gcd_degree (k : ℕ) :
    (gcd (orbit (f : ℚ[X]) k) (orbit g (2 * k))).natDegree = 2 ^ k := by
  have hf : orbit (f : ℚ[X]) k ≠ 0 := by rw [f_orbit]; exact pow_ne_zero _ X_ne_zero
  have hgcd : gcd (orbit (f : ℚ[X]) k) (orbit g (2 * k)) ≠ 0 := by
    intro h
    exact hf ((gcd_eq_zero_iff _ _).mp h).1
  have hd : orbit (f : ℚ[X]) k ∣ orbit g (2 * k) := by
    rw [f_orbit]
    exact common_factor k
  apply le_antisymm
  · simpa [f_orbit] using natDegree_le_of_dvd (gcd_dvd_left _ _) hf
  · simpa [f_orbit] using natDegree_le_of_dvd (dvd_gcd (dvd_refl _) hd) hgcd

theorem polynomial_unbounded : ∀ B : ℕ, ∃ n m : ℕ,
    B < (gcd (orbit (f : ℚ[X]) n) (orbit g m)).natDegree := by
  intro B
  exact ⟨B, 2 * B, by rw [polynomial_gcd_degree]; exact B.lt_two_pow_self⟩

/-- The same actual integer polynomials, evaluated at the nonzero starting point 2. -/
theorem evaluated_gcd (k : ℕ) :
    Int.gcd ((orbit (f : ℤ[X]) k).eval 2) ((orbit g (2 * k)).eval 2) = 2 ^ (2 ^ k) := by
  have hd : (orbit (f : ℤ[X]) k).eval 2 ∣ (orbit g (2 * k)).eval 2 := by
    apply eval_dvd
    rw [f_orbit]
    exact common_factor k
  rw [Int.gcd_eq_left hd, f_orbit]
  simp [Int.natAbs_pow]

theorem evaluated_unbounded : ∀ B : ℕ, ∃ n m : ℕ,
    B < Int.gcd ((orbit (f : ℤ[X]) n).eval 2) ((orbit g m).eval 2) := by
  intro B
  refine ⟨B, 2 * B, ?_⟩
  rw [evaluated_gcd]
  exact lt_trans B.lt_two_pow_self (2 ^ B).lt_two_pow_self

theorem counterexample : IsCoprime (f : ℚ[X]) g ∧
    (f : ℚ[X]).natDegree = 2 ∧ (g : ℚ[X]).natDegree = 2 ∧
    (∀ B : ℕ, ∃ n m : ℕ, B < (gcd (orbit (f : ℚ[X]) n) (orbit g m)).natDegree) ∧
    (∀ B : ℕ, ∃ n m : ℕ,
      B < Int.gcd ((orbit (f : ℤ[X]) n).eval 2) ((orbit g m).eval 2)) :=
  ⟨initial_coprime, fixed_degrees.1, fixed_degrees.2, polynomial_unbounded, evaluated_unbounded⟩

end
end CoprimeOrbitCounterexample

#print axioms CoprimeOrbitCounterexample.initial_coprime
#print axioms CoprimeOrbitCounterexample.f_orbit
#print axioms CoprimeOrbitCounterexample.common_factor
#print axioms CoprimeOrbitCounterexample.polynomial_gcd_degree
#print axioms CoprimeOrbitCounterexample.evaluated_gcd
#print axioms CoprimeOrbitCounterexample.counterexample
