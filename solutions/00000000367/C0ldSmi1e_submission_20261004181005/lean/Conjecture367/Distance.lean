import Conjecture367.Definitions
import Mathlib.Algebra.Order.Round
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

noncomputable section
open Filter
open scoped Topology

namespace Conjecture367

/-- The infimum over the full integer set is attained by the nearest integer. -/
theorem distanceToIntegers_eq_round (x : ℝ) :
    distanceToIntegers x = |x - (round x : ℝ)| := by
  unfold distanceToIntegers
  apply le_antisymm
  · simpa only [Real.dist_eq] using
      (Metric.infDist_le_dist_of_mem (x := x) (s := Set.range (Int.cast : ℤ → ℝ))
        (show (round x : ℝ) ∈ Set.range (Int.cast : ℤ → ℝ) from ⟨round x, rfl⟩))
  · apply (Metric.le_infDist (Set.range_nonempty (Int.cast : ℤ → ℝ))).mpr
    rintro y ⟨z, rfl⟩
    simpa only [Real.dist_eq] using round_le x z

theorem distanceToIntegers_intCast (z : ℤ) : distanceToIntegers (z : ℝ) = 0 :=
  Metric.infDist_zero_of_mem ⟨z, rfl⟩

theorem third_pow_le_third (n : ℕ) (hn : 1 ≤ n) : (1 / 3 : ℝ) ^ n ≤ 1 / 3 := by
  cases n with
  | zero => omega
  | succ m =>
    rw [pow_succ]
    have hm : (1 / 3 : ℝ) ^ m ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    nlinarith

theorem round_third_pow (n : ℕ) (hn : 1 ≤ n) : round ((1 / 3 : ℝ) ^ n) = 0 := by
  apply round_eq_zero_iff.mpr
  constructor
  · have h : 0 < (1 / 3 : ℝ) ^ n := pow_pos (by norm_num) n
    linarith
  · have h := third_pow_le_third n hn
    linarith

theorem round_sequence_third (n : ℕ) (hn : 1 ≤ n) :
    round (sequence (1 / 3) n) = (2 : ℤ) ^ n := by
  have hcast : (2 : ℝ) ^ n = (((2 : ℤ) ^ n : ℤ) : ℝ) := by norm_cast
  rw [sequence, hcast, round_intCast_add, round_third_pow n hn, add_zero]

/-- Every positive-index term has the exact, strictly positive distance `3⁻ⁿ`. -/
theorem distance_sequence_third (n : ℕ) (hn : 1 ≤ n) :
    distanceToIntegers (sequence (1 / 3) n) = (1 / 3 : ℝ) ^ n := by
  rw [distanceToIntegers_eq_round, round_sequence_third n hn]
  simp only [sequence, Int.cast_pow, Int.cast_ofNat, add_sub_cancel_left]
  exact abs_of_pos (pow_pos (by norm_num : (0 : ℝ) < 1 / 3) n)

theorem distance_sequence_third_pos (n : ℕ) (hn : 1 ≤ n) :
    0 < distanceToIntegers (sequence (1 / 3) n) := by
  rw [distance_sequence_third n hn]
  positivity

theorem sequence_third_not_integer (n : ℕ) (hn : 1 ≤ n) :
    sequence (1 / 3) n ∉ Set.range (Int.cast : ℤ → ℝ) := by
  intro h
  have hz : distanceToIntegers (sequence (1 / 3) n) = 0 := Metric.infDist_zero_of_mem h
  have hp := distance_sequence_third_pos n hn
  linarith

theorem sequence_third_ne_intCast (n : ℕ) (hn : 1 ≤ n) (z : ℤ) :
    sequence (1 / 3) n ≠ (z : ℝ) := by
  intro h
  exact sequence_third_not_integer n hn ⟨z, h.symm⟩

theorem sequence_third_rational (n : ℕ) : ∃ q : ℚ, sequence (1 / 3) n = (q : ℝ) := by
  refine ⟨(2 : ℚ) ^ n + (1 / 3 : ℚ) ^ n, ?_⟩
  push_cast
  rfl

theorem sequence_tendsto_atTop {r : ℝ} (hr : 0 ≤ r) :
    Tendsto (sequence r) atTop atTop := by
  apply tendsto_atTop_mono (f := fun n : ℕ => (2 : ℝ) ^ n)
    (fun n => le_add_of_nonneg_right (pow_nonneg hr n))
  exact tendsto_pow_atTop_atTop_of_one_lt (by norm_num)

theorem sequence_third_tendsto_atTop : Tendsto (sequence (1 / 3)) atTop atTop :=
  sequence_tendsto_atTop (by norm_num)

theorem sequence_three_integer (n : ℕ) :
    sequence 3 n = (((2 : ℤ) ^ n + (3 : ℤ) ^ n : ℤ) : ℝ) := by
  push_cast
  rfl

theorem distance_sequence_three (n : ℕ) : distanceToIntegers (sequence 3 n) = 0 := by
  rw [sequence_three_integer, distanceToIntegers_intCast]

end Conjecture367
