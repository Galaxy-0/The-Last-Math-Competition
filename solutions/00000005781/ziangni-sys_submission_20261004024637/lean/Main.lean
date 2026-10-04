import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

namespace DivergenceCounterexample

noncomputable def potential (x : ℝ) : ℝ := x ^ 2 / 2

theorem potential_derivative (x : ℝ) : HasDerivAt potential x x := by
  convert (hasDerivAt_pow 2 x).div_const 2 using 1
  simp [potential]

theorem dual_coordinate (x : ℝ) : deriv potential x = x :=
  (potential_derivative x).deriv

theorem hessian_one (x : ℝ) : deriv (deriv potential) x = 1 := by
  have h : deriv potential = fun y => y := funext dual_coordinate
  rw [h]
  exact deriv_id x

-- An explicit strict Jensen gap certifies strict convexity of the potential.
theorem jensen_gap (x y t : ℝ) :
    (1 - t) * potential x + t * potential y -
      potential ((1 - t) * x + t * y) =
      t * (1 - t) * (x - y) ^ 2 / 2 := by
  unfold potential
  ring

theorem strict_convexity (x y t : ℝ) (hxy : x ≠ y) (ht : 0 < t) (ht1 : t < 1) :
    potential ((1 - t) * x + t * y) <
      (1 - t) * potential x + t * potential y := by
  have hs : 0 < (x - y)^2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hxy)
  have hp : 0 < t * (1 - t) * (x - y)^2 / 2 :=
    div_pos (mul_pos (mul_pos ht (sub_pos.mpr ht1)) hs) (by norm_num)
  have h := jensen_gap x y t
  linarith

-- Completing the square proves the actual Legendre-dual maximizing formula.
theorem legendre_gap (x eta : ℝ) :
    potential eta - (eta * x - potential x) = (x - eta)^2 / 2 := by
  unfold potential
  ring

theorem legendre_max (x eta : ℝ) :
    eta * x - potential x ≤ potential eta := by
  have h := legendre_gap x eta
  have hs : 0 ≤ (x - eta)^2 / 2 := div_nonneg (sq_nonneg _) (by norm_num)
  linarith

theorem legendre_attains (eta : ℝ) :
    eta * eta - potential eta = potential eta := by
  unfold potential
  ring

noncomputable def canonicalDivergence (x y : ℝ) : ℝ :=
  potential x + potential (deriv potential y) - x * deriv potential y

noncomputable def bregmanDivergence (x y : ℝ) : ℝ :=
  potential x - potential y - deriv potential y * (x - y)

theorem canonical_is_bregman (x y : ℝ) :
    canonicalDivergence x y = bregmanDivergence x y := by
  simp only [canonicalDivergence, bregmanDivergence, dual_coordinate, potential]
  ring

theorem divergence_formula (x y : ℝ) :
    canonicalDivergence x y = (x - y)^2 / 2 := by
  simp only [canonicalDivergence, dual_coordinate, potential]
  ring

theorem divergence_nonnegative (x y : ℝ) : 0 ≤ canonicalDivergence x y := by
  rw [divergence_formula]
  exact div_nonneg (sq_nonneg _) (by norm_num)

noncomputable def triangleDeficit (x y z : ℝ) : ℝ :=
  canonicalDivergence x y + canonicalDivergence y z - canonicalDivergence x z

theorem three_point_identity (x y z : ℝ) :
    triangleDeficit x y z = (y - x) * (y - z) := by
  simp only [triangleDeficit, divergence_formula]
  ring

theorem negative_triangle_deficit : triangleDeficit 0 1 2 = -1 := by
  rw [three_point_identity]
  norm_num

theorem positive_triangle_deficit : triangleDeficit 0 2 1 = 2 := by
  rw [three_point_identity]
  norm_num

theorem conjecture_5781_false :
    ¬ (∀ x y z : ℝ, 0 ≤ triangleDeficit x y z) := by
  intro h
  have hn := h 0 1 2
  rw [negative_triangle_deficit] at hn
  norm_num at hn

theorem opposite_sign_also_false :
    ¬ (∀ x y z : ℝ, 0 ≤ -triangleDeficit x y z) := by
  intro h
  have hn := h 0 2 1
  rw [positive_triangle_deficit] at hn
  norm_num at hn

end DivergenceCounterexample

#print axioms DivergenceCounterexample.conjecture_5781_false
#print axioms DivergenceCounterexample.opposite_sign_also_false
#print axioms DivergenceCounterexample.hessian_one
#print axioms DivergenceCounterexample.strict_convexity
