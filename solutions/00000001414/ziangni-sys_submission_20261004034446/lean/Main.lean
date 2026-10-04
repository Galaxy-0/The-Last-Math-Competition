import Mathlib.NumberTheory.Bernoulli
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

namespace BernoulliOrderCounterexample
open Finset
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem b0 : bernoulli' 0 = (1 : ℚ) := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, Nat.choose]

theorem b1 : bernoulli' 1 = (1/2 : ℚ) := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, Nat.choose, b0]

theorem b2 : bernoulli' 2 = (1/6 : ℚ) := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, Nat.choose, b0, b1]

theorem b3 : bernoulli' 3 = (0 : ℚ) := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, Nat.choose, b0, b1, b2]

theorem b4 : bernoulli' 4 = (-1/30 : ℚ) := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, Nat.choose, b0, b1, b2, b3]

theorem b5 : bernoulli' 5 = (0 : ℚ) := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, Nat.choose, b0, b1, b2, b3, b4]

theorem b6 : bernoulli' 6 = (1/42 : ℚ) := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, Nat.choose, b0, b1, b2, b3, b4, b5]

theorem b7 : bernoulli' 7 = (0 : ℚ) := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, Nat.choose, b0, b1, b2, b3, b4, b5, b6]

theorem b8 : bernoulli' 8 = (-1/30 : ℚ) := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, Nat.choose, b0, b1, b2, b3, b4, b5, b6, b7]

theorem b9 : bernoulli' 9 = (0 : ℚ) := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, Nat.choose, b0, b1, b2, b3, b4, b5, b6, b7, b8]

theorem b10 : bernoulli' 10 = (5/66 : ℚ) := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, Nat.choose, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9]

theorem b11 : bernoulli' 11 = (0 : ℚ) := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, Nat.choose, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10]

theorem b12 : bernoulli' 12 = (-691/2730 : ℚ) := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, Nat.choose, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11]

theorem bernoulli_twelve : bernoulli 12 = (-691/2730 : ℚ) := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide)]
  exact b12

def displayedValue : ℚ := bernoulli 12 / (2 * (Nat.factorial 6 : ℚ))
def absoluteValue : ℚ := |bernoulli 12| / (2 * (Nat.factorial 6 : ℚ))
def parentheticalValue : ℚ := 691 / (2^3 * 3^2 * 5 * (Nat.factorial 6 : ℚ))

theorem displayed_value : displayedValue = (-691/3931200 : ℚ) := by
  norm_num [displayedValue, bernoulli_twelve, Nat.factorial]
theorem absolute_value : absoluteValue = (691/3931200 : ℚ) := by
  rw [absoluteValue, bernoulli_twelve, abs_of_neg (by norm_num : (-691/2730 : ℚ) < 0)]
  norm_num [Nat.factorial]
theorem parenthetical_value : parentheticalValue = (691/259200 : ℚ) := by
  norm_num [parentheticalValue, Nat.factorial]

theorem no_natural_in_open_unit_interval {q : ℚ} (h0 : 0 < q) (h1 : q < 1)
    (n : ℕ) : (n : ℚ) ≠ q := by
  intro h
  cases n with
  | zero => norm_num at h; linarith
  | succ m => have hm : (0 : ℚ) ≤ m := Nat.cast_nonneg m
              push_cast at h
              linarith

theorem all_fractions_nonintegral (n : ℕ) :
    (n : ℚ) ≠ displayedValue ∧ (n : ℚ) ≠ absoluteValue ∧
    (n : ℚ) ≠ parentheticalValue := by
  constructor
  · intro h
    have hn : (0 : ℚ) ≤ n := Nat.cast_nonneg n
    rw [displayed_value] at h
    linarith
  constructor
  · rw [absolute_value]
    exact no_natural_in_open_unit_interval (by norm_num) (by norm_num) n
  · rw [parenthetical_value]
    exact no_natural_in_open_unit_interval (by norm_num) (by norm_num) n

-- This applies to every finite group, independently of any K-theory identification.
theorem finite_group_orders_impossible (G : Type*) [Group G] [Fintype G] :
    (Fintype.card G : ℚ) ≠ displayedValue ∧
    (Fintype.card G : ℚ) ≠ absoluteValue ∧
    (Fintype.card G : ℚ) ≠ parentheticalValue :=
  all_fractions_nonintegral (Fintype.card G)

-- A literal finite-group-order interpretation of the displayed equality.
def DisplayedOrderClaim : Prop := ∃ (G : Type) (_ : Group G) (_ : Fintype G),
  (Fintype.card G : ℚ) = displayedValue

theorem conjecture_00000001414_displayed_equality_false : ¬ DisplayedOrderClaim := by
  rintro ⟨G, hG, hF, h⟩
  exact (all_fractions_nonintegral (Fintype.card G)).1 h

#print axioms bernoulli_twelve
#print axioms all_fractions_nonintegral
#print axioms finite_group_orders_impossible
#print axioms conjecture_00000001414_displayed_equality_false
end BernoulliOrderCounterexample
