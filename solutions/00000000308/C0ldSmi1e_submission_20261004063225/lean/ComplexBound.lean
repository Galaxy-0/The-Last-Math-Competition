import Definitions
import RealBound
import Mathlib.Tactic

namespace Conjecture308

/-- One nonzero coordinate of a Gaussian denominator already gives a uniform
lower bound for the complex linear error. -/
theorem gaussian_sqrt_two_linear_bound (p q : GaussianInt) (hq : q ≠ 0) :
    (1 / 4 : ℝ) ≤ ‖(q : ℂ)‖ * ‖(q : ℂ) * (Real.sqrt 2 : ℂ) - (p : ℂ)‖ := by
  have hc : q.re ≠ 0 ∨ q.im ≠ 0 := by
    by_contra! h
    apply hq
    exact Zsqrtd.ext h.1 h.2
  rcases hc with hre | him
  · have hreal := real_sqrt_two_bound q.re p.re hre
    have hqre : |(q.re : ℝ)| ≤ ‖(q : ℂ)‖ := by
      simpa only [← GaussianInt.to_real_re] using Complex.abs_re_le_norm (q : ℂ)
    have herrore : |(q.re : ℝ) * Real.sqrt 2 - (p.re : ℝ)| ≤
        ‖(q : ℂ) * (Real.sqrt 2 : ℂ) - (p : ℂ)‖ := by
      simpa only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        mul_zero, sub_zero, ← GaussianInt.to_real_re] using
        Complex.abs_re_le_norm ((q : ℂ) * (Real.sqrt 2 : ℂ) - (p : ℂ))
    exact hreal.trans (mul_le_mul hqre herrore (abs_nonneg _) (norm_nonneg _))
  · have hreal := real_sqrt_two_bound q.im p.im him
    have hqim : |(q.im : ℝ)| ≤ ‖(q : ℂ)‖ := by
      simpa only [← GaussianInt.to_real_im] using Complex.abs_im_le_norm (q : ℂ)
    have herrorim : |(q.im : ℝ) * Real.sqrt 2 - (p.im : ℝ)| ≤
        ‖(q : ℂ) * (Real.sqrt 2 : ℂ) - (p : ℂ)‖ := by
      simpa only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        mul_zero, zero_add, ← GaussianInt.to_real_im] using
        Complex.abs_im_le_norm ((q : ℂ) * (Real.sqrt 2 : ℂ) - (p : ℂ))
    exact hreal.trans (mul_le_mul hqim herrorim (abs_nonneg _) (norm_nonneg _))

/-- The usual Gaussian-rational approximation inequality holds with constant `1/4`. -/
theorem gaussian_sqrt_two_approximation_bound (p q : GaussianInt) (hq : q ≠ 0) :
    (1 / 4 : ℝ) / ‖(q : ℂ)‖ ^ 2 ≤ ‖(Real.sqrt 2 : ℂ) - (p : ℂ) / (q : ℂ)‖ := by
  have hqc : (q : ℂ) ≠ 0 := GaussianInt.toComplex_eq_zero.not.mpr hq
  have hqn : 0 < ‖(q : ℂ)‖ := norm_pos_iff.mpr hqc
  have hid : (q : ℂ) * (Real.sqrt 2 : ℂ) - (p : ℂ) =
      (q : ℂ) * ((Real.sqrt 2 : ℂ) - (p : ℂ) / (q : ℂ)) := by
    field_simp
    ring
  have hlinear := gaussian_sqrt_two_linear_bound p q hq
  rw [hid, norm_mul] at hlinear
  apply (div_le_iff₀ (sq_pos_of_pos hqn)).mpr
  nlinarith [hlinear]

/-- The real number `√2`, embedded in `ℂ`, is badly approximable by all Gaussian rationals. -/
theorem sqrt_two_mem_BadC : (Real.sqrt 2 : ℂ) ∈ BadC := by
  refine ⟨1 / 4, by norm_num, ?_⟩
  exact gaussian_sqrt_two_approximation_bound

end Conjecture308
