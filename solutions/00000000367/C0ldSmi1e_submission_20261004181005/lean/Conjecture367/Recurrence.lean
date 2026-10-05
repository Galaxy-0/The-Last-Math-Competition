import Conjecture367.Definitions
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Tactic

noncomputable section
open Polynomial

namespace Conjecture367

@[simp] theorem recurrence_order (r : ℝ) : (recurrence r).order = 2 := rfl

/-- Both exponential summands solve the stated second-order recurrence. -/
theorem sequence_isSolution (r : ℝ) :
    (recurrence r).IsSolution (sequence r) := by
  intro n
  simp [recurrence, sequence, Fin.sum_univ_two, pow_add]
  ring

/-- This is the characteristic polynomial of the actual recurrence object. -/
theorem recurrence_charPoly (r : ℝ) :
    (recurrence r).charPoly = (X - C 2) * (X - C r) := by
  simp [LinearRecurrence.charPoly, recurrence, Fin.sum_univ_two,
    ← C_mul_X_pow_eq_monomial]
  ring

theorem recurrence_complex_charPoly (r : ℝ) :
    (recurrence r).charPoly.map Complex.ofRealHom =
      (X - C (2 : ℂ)) * (X - C (r : ℂ)) := by
  rw [recurrence_charPoly]
  simp

/-- The full complex root set consists exactly of the two displayed roots. -/
theorem recurrence_complex_root_iff (r : ℝ) (z : ℂ) :
    ((recurrence r).charPoly.map Complex.ofRealHom).IsRoot z ↔
      z = 2 ∨ z = (r : ℂ) := by
  rw [recurrence_complex_charPoly]
  simp [Polynomial.IsRoot.def, mul_eq_zero, sub_eq_zero]

/-- The first three terms exclude every recurrence of order zero or one. -/
theorem recurrence_minimal (r : ℝ) (hr : r ≠ 2) :
    IsMinimalRecurrence (recurrence r) (sequence r) := by
  refine ⟨sequence_isSolution r, ?_⟩
  rintro ⟨d, a⟩ h
  change 2 ≤ d
  rcases d with _ | d
  · have h0 := h 0
    norm_num [LinearRecurrence.IsSolution, sequence] at h0
  rcases d with _ | d
  · have h0 := h 0
    have h1 := h 1
    norm_num [LinearRecurrence.IsSolution, sequence, Fin.sum_univ_succ] at h0 h1
    have hsq : (r - 2) ^ 2 = 0 := by nlinarith
    have := pow_eq_zero hsq
    exact False.elim (hr (sub_eq_zero.mp this))
  · omega

/-- Positive, distinct real roots cannot have a root-of-unity quotient. -/
theorem recurrence_nondegenerate (r : ℝ) (hr : 0 < r) (hr2 : r ≠ 2) :
    Nondegenerate (recurrence r) := by
  constructor
  · intro a ha
    rcases (recurrence_complex_root_iff r a).mp ha with rfl | rfl
    · norm_num
    · exact_mod_cast ne_of_gt hr
  · intro a b ha hb hab horder
    rcases (recurrence_complex_root_iff r a).mp ha with rfl | rfl <;>
      rcases (recurrence_complex_root_iff r b).mp hb with rfl | rfl
    · exact hab rfl
    · have hn := horder.norm_eq_one
      rw [norm_div, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hr] at hn
      have : r = 2 := by
        have := (div_eq_iff (ne_of_gt hr)).mp hn
        linarith
      exact hr2 this
    · have hn := horder.norm_eq_one
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
        Complex.norm_ofNat] at hn
      have : r = 2 := by linarith [(div_eq_iff (by norm_num : (2 : ℝ) ≠ 0)).mp hn]
      exact hr2 this
    · exact hab rfl

theorem rational_recurrence_minimal :
    IsMinimalRecurrence (recurrence (1 / 3)) (sequence (1 / 3)) :=
  recurrence_minimal _ (by norm_num)

theorem rational_recurrence_nondegenerate :
    Nondegenerate (recurrence (1 / 3)) :=
  recurrence_nondegenerate _ (by norm_num) (by norm_num)

/-- The principal counterexample has rational recurrence coefficients. -/
theorem rational_recurrence_coefficients :
    (recurrence (1 / 3)).coeffs =
      fun i => ((![(-2 / 3 : ℚ), 7 / 3] i : ℚ) : ℝ) := by
  change ![(-2 * (1 / 3) : ℝ), 2 + 1 / 3] = _
  ext i
  fin_cases i <;> norm_num

theorem integer_recurrence_minimal :
    IsMinimalRecurrence (recurrence 3) (sequence 3) :=
  recurrence_minimal _ (by norm_num)

theorem integer_recurrence_nondegenerate :
    Nondegenerate (recurrence 3) :=
  recurrence_nondegenerate _ (by norm_num) (by norm_num)

/-- The supplementary example even has integer recurrence coefficients. -/
theorem integer_recurrence_coefficients :
    (recurrence 3).coeffs = fun i => ((![(-6 : ℤ), 5] i : ℤ) : ℝ) := by
  change ![(-2 * 3 : ℝ), 2 + 3] = _
  ext i
  fin_cases i <;> norm_num

end Conjecture367
