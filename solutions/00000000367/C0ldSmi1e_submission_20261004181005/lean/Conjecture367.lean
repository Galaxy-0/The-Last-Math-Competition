import Conjecture367.Recurrence
import Conjecture367.Distance
import Conjecture367.Asymptotics

noncomputable section
open Filter
open scoped Topology

namespace Conjecture367

/-- Every real exponent gives the opposite inequality on a full tail. -/
theorem distance_eventually_lt_power (C : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      distanceToIntegers (sequence (1 / 3) n) < (n : ℝ) ^ (-C) := by
  filter_upwards [third_pow_eventually_lt_rpow_neg C, eventually_ge_atTop (1 : ℕ)]
    with n hn hn1
  rwa [distance_sequence_third n hn1]

theorem no_polynomial_lower_bound_third :
    ¬ HasPolynomialLowerBound (sequence (1 / 3)) := by
  rintro ⟨C, N, h⟩
  obtain ⟨n, hnN, hn1, hn⟩ := ((eventually_ge_atTop N).and
    ((eventually_ge_atTop (1 : ℕ)).and (distance_eventually_lt_power C))).exists
  exact (not_lt_of_ge hn.le) (h n hnN (by omega))

/-- The integer-coefficient example also fails at every positive index. -/
theorem no_polynomial_lower_bound_three :
    ¬ HasPolynomialLowerBound (sequence 3) := by
  rintro ⟨C, N, h⟩
  have hnpos : (0 : ℝ) < (N + 1 : ℕ) := by positivity
  have hp := Real.rpow_pos_of_pos hnpos (-C)
  have hh := h (N + 1) (by omega) (by omega)
  rw [distance_sequence_three] at hh
  linarith

/-- The source's lower-bound existence claim is false. -/
theorem conjecture_false : ¬ ClaimedLowerBound := by
  intro h
  exact no_polynomial_lower_bound_third
    (h (recurrence (1 / 3)) (sequence (1 / 3)) (by norm_num [recurrence])
      rational_recurrence_minimal rational_recurrence_nondegenerate)

/-- A second disproof using a monic integer-coefficient recurrence. -/
theorem conjecture_false_integer_example : ¬ ClaimedLowerBound := by
  intro h
  exact no_polynomial_lower_bound_three
    (h (recurrence 3) (sequence 3) (by norm_num [recurrence])
      integer_recurrence_minimal integer_recurrence_nondegenerate)

end Conjecture367
