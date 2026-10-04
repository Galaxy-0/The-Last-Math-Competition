import Mathlib.Data.Real.Irrational
import Mathlib.Tactic

namespace Conjecture308

/-- An explicit uniform irrationality bound for sqrt(2) with integer coefficients. -/
theorem real_sqrt_two_bound (m n : ℤ) (hm : m ≠ 0) :
    (1 / 4 : ℝ) ≤ |(m : ℝ)| * |(m : ℝ) * Real.sqrt 2 - (n : ℝ)| := by
  have hmone : (1 : ℝ) ≤ |(m : ℝ)| := by exact_mod_cast Int.one_le_abs hm
  have hroot : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hroot_sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hroot_lt : Real.sqrt 2 < 3 / 2 := by nlinarith
  have hirr : Irrational ((m : ℝ) * Real.sqrt 2) :=
    irrational_intCast_mul_iff.mpr ⟨hm, irrational_sqrt_two⟩
  have hfactor :
      ((m : ℝ) * Real.sqrt 2 - (n : ℝ)) *
        ((m : ℝ) * Real.sqrt 2 + (n : ℝ)) = ((2 * m ^ 2 - n ^ 2 : ℤ) : ℝ) := by
    push_cast
    calc
      _ = (m : ℝ) ^ 2 * (Real.sqrt 2) ^ 2 - (n : ℝ) ^ 2 := by ring
      _ = _ := by rw [hroot_sq]; ring
  have hnorm_ne : (2 * m ^ 2 - n ^ 2 : ℤ) ≠ 0 := by
    intro hzero
    have hzeroR : ((2 * m ^ 2 - n ^ 2 : ℤ) : ℝ) = 0 := by exact_mod_cast hzero
    rw [← hfactor] at hzeroR
    rcases mul_eq_zero.mp hzeroR with h | h
    · exact hirr.ne_int n (sub_eq_zero.mp h)
    · apply hirr.ne_int (-n)
      push_cast
      linarith
  have hone : (1 : ℝ) ≤
      |(m : ℝ) * Real.sqrt 2 - (n : ℝ)| *
        |(m : ℝ) * Real.sqrt 2 + (n : ℝ)| := by
    rw [← abs_mul, hfactor]
    exact_mod_cast Int.one_le_abs hnorm_ne
  by_cases he : 1 ≤ |(m : ℝ) * Real.sqrt 2 - (n : ℝ)|
  · nlinarith [mul_le_mul hmone he (by norm_num : (0 : ℝ) ≤ 1) (abs_nonneg (m : ℝ))]
  · have herr : |(m : ℝ) * Real.sqrt 2 - (n : ℝ)| < 1 := lt_of_not_ge he
    have hplus : |(m : ℝ) * Real.sqrt 2 + (n : ℝ)| ≤
        2 * |(m : ℝ)| * Real.sqrt 2 + |(m : ℝ) * Real.sqrt 2 - (n : ℝ)| := by
      calc
        _ = |2 * ((m : ℝ) * Real.sqrt 2) -
          ((m : ℝ) * Real.sqrt 2 - (n : ℝ))| := by congr 1; ring
        _ ≤ |2 * ((m : ℝ) * Real.sqrt 2)| +
          |(m : ℝ) * Real.sqrt 2 - (n : ℝ)| := abs_sub _ _
        _ = _ := by rw [abs_mul, abs_mul, abs_of_nonneg hroot]; norm_num; ring
    have hconj : |(m : ℝ) * Real.sqrt 2 + (n : ℝ)| ≤ 4 * |(m : ℝ)| := by
      nlinarith [mul_le_mul_of_nonneg_left hroot_lt.le (abs_nonneg (m : ℝ))]
    have hmul := mul_le_mul_of_nonneg_left hconj
      (abs_nonneg ((m : ℝ) * Real.sqrt 2 - (n : ℝ)))
    nlinarith


end Conjecture308
