import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Tactic

/-! Consecutive negative coefficients obstruct strict and even weak sign alternation. -/
namespace Conjecture4107

/-- Read every coefficient from the constant term through the leading term. -/
def StrictSignAlternation (p : Polynomial ℤ) : Prop :=
  ∀ k : ℕ, k < p.natDegree → p.coeff k * p.coeff (k + 1) < 0

/-- A weaker necessary adjacent-sign condition, allowing zero coefficients. -/
def WeakSignAlternation (p : Polynomial ℤ) : Prop :=
  ∀ k : ℕ, k < p.natDegree → p.coeff k * p.coeff (k + 1) ≤ 0

theorem strict_implies_weak {p : Polynomial ℤ} (h : StrictSignAlternation p) :
    WeakSignAlternation p := fun k hk => le_of_lt (h k hk)

/-- The degree condition follows from the nonzero second coefficient. -/
theorem negative_pair_obstructs_weak {p : Polynomial ℤ} {k : ℕ}
    (hi : p.coeff k < 0) (hj : p.coeff (k + 1) < 0) :
    ¬ WeakSignAlternation p := by
  intro h
  have hd := Polynomial.le_natDegree_of_ne_zero (ne_of_lt hj)
  have hk : k < p.natDegree := by omega
  have hp : 0 < p.coeff k * p.coeff (k + 1) := mul_pos_of_neg_of_neg hi hj
  exact (not_lt_of_ge (h k hk)) hp

theorem negative_pair_obstructs_strict {p : Polynomial ℤ} {k : ℕ}
    (hi : p.coeff k < 0) (hj : p.coeff (k + 1) < 0) :
    ¬ StrictSignAlternation p :=
  fun h => negative_pair_obstructs_weak hi hj (strict_implies_weak h)

end Conjecture4107
