import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

namespace EisensteinCounterexample
noncomputable def omega : ℂ := ⟨-1 / 2, Real.sqrt 3 / 2⟩
noncomputable def embed (a b : ℤ) : ℂ := (a : ℂ) + (b : ℂ) * omega

theorem omega_quadratic : omega ^ 2 + omega + 1 = 0 := by
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  apply Complex.ext <;> simp [omega, pow_two, Complex.mul_re, Complex.mul_im]
  · nlinarith
  · ring

theorem omega_primitive : omega ^ 3 = 1 ∧ omega ≠ 1 := by
  constructor
  · calc
      omega ^ 3 = (omega - 1) * (omega ^ 2 + omega + 1) + 1 := by ring
      _ = 1 := by rw [omega_quadratic]; ring
  · intro h
    have := congrArg Complex.re h
    norm_num [omega] at this

theorem embedded_norm (a b : ℤ) :
    Complex.normSq (embed a b) = (a : ℝ)^2 - (a : ℝ)*(b : ℝ) + (b : ℝ)^2 := by
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  simp only [embed, omega, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.intCast_re, Complex.intCast_im]
  ring_nf
  rw [hs]
  ring

def ClaimedNormFormula : Prop := ∀ a b : ℤ,
  Complex.normSq (embed a b) = (a : ℝ)^2 + (b : ℝ)^2

theorem witness : Complex.normSq (embed 1 1) = 1 := by
  rw [embedded_norm]; norm_num

theorem conjecture_false : ¬ ClaimedNormFormula := by
  intro h
  have hw := h 1 1
  rw [witness] at hw
  norm_num at hw

#print axioms omega_quadratic
#print axioms omega_primitive
#print axioms embedded_norm
#print axioms witness
#print axioms conjecture_false
end EisensteinCounterexample
