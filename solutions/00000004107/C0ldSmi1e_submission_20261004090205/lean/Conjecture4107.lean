import Conjecture4107.Arrangement
import Conjecture4107.Signs

/-! The actual characteristic polynomial has two consecutive negative coefficients. -/
noncomputable section
namespace Conjecture4107

/-- The stated universal sign-alternation clause for finite real subspace arrangements. -/
def ConjectureClaim : Prop :=
  ∀ (n m : ℕ) (A : Fin m → Submodule ℝ (Fin n → ℝ)),
    StrictSignAlternation (characteristicPolynomial A)

@[simp] theorem coefficient_zero : (characteristicPolynomial arrangement).coeff 0 = 1 := by
  rw [characteristicPolynomial_arrangement]
  norm_num [Polynomial.coeff_one, Polynomial.coeff_X]

@[simp] theorem coefficient_one : (characteristicPolynomial arrangement).coeff 1 = -1 := by
  rw [characteristicPolynomial_arrangement]
  norm_num [Polynomial.coeff_one, Polynomial.coeff_X]

@[simp] theorem coefficient_two : (characteristicPolynomial arrangement).coeff 2 = -1 := by
  rw [characteristicPolynomial_arrangement]
  norm_num [Polynomial.coeff_one, Polynomial.coeff_X]

@[simp] theorem coefficient_three : (characteristicPolynomial arrangement).coeff 3 = 1 := by
  rw [characteristicPolynomial_arrangement]
  norm_num [Polynomial.coeff_one, Polynomial.coeff_X]

theorem arrangement_not_weak_alternating :
    ¬ WeakSignAlternation (characteristicPolynomial arrangement) := by
  apply negative_pair_obstructs_weak (k := 1) <;> norm_num

theorem arrangement_not_strict_alternating :
    ¬ StrictSignAlternation (characteristicPolynomial arrangement) := by
  apply negative_pair_obstructs_strict (k := 1) <;> norm_num

/-- The universal claim fails for the two actual subspaces of real three-dimensional space. -/
theorem conjecture4107_disproof : ¬ ConjectureClaim := by
  intro h
  exact arrangement_not_strict_alternating (h 3 2 arrangement)

end Conjecture4107
