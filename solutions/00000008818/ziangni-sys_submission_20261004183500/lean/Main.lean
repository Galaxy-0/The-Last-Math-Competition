import Mathlib.Analysis.Convex.SpecificFunctions.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

open Set Filter
open scoped Topology
noncomputable section
namespace BFGS

def f (x : ℝ) := x ^ 4
def g (x : ℝ) := 4 * x ^ 3

theorem smooth : ContDiff ℝ ⊤ f := contDiff_id.pow 4

theorem gradient (x : ℝ) : HasDerivAt f (g x) x := by
  simpa [f, g] using (hasDerivAt_id x).pow 4

theorem strict_convex : StrictConvexOn ℝ univ f :=
  (show Even (4 : ℕ) by decide).strictConvexOn_pow (by decide)

theorem minimizer (x : ℝ) : f 0 ≤ f x ∧ (f x = f 0 ↔ x = 0) := by
  simp only [f, zero_pow (by decide : 4 ≠ 0)]
  exact ⟨by positivity, pow_eq_zero_iff (by decide)⟩

theorem degenerate_hessian : deriv g 0 = 0 := by
  have h := ((hasDerivAt_id (0 : ℝ)).pow 3).const_mul 4
  have hg : HasDerivAt g 0 0 := by convert h using 1 <;> norm_num
  exact hg.deriv

theorem root_exists : ∃ r : ℝ, 3 / 4 ≤ r ∧ r ≤ 4 / 5 ∧ r ^ 3 + r ^ 2 = 1 := by
  have h := intermediate_value_Icc (show (3 / 4 : ℝ) ≤ 4 / 5 by norm_num)
    (f := fun r : ℝ => r ^ 3 + r ^ 2)
    ((continuous_id.pow 3).add (continuous_id.pow 2)).continuousOn
    (show (1 : ℝ) ∈ Icc ((3 / 4 : ℝ) ^ 3 + (3 / 4 : ℝ) ^ 2)
      ((4 / 5 : ℝ) ^ 3 + (4 / 5 : ℝ) ^ 2) by norm_num)
  rcases h with ⟨r, hr, he⟩
  exact ⟨r, hr.1, hr.2, he⟩

def r : ℝ := Classical.choose root_exists
theorem r_spec : 3 / 4 ≤ r ∧ r ≤ 4 / 5 ∧ r ^ 3 + r ^ 2 = 1 :=
  Classical.choose_spec root_exists

theorem r_pos : 0 < r := by linarith [r_spec.1]
theorem r_lt_one : r < 1 := by linarith [r_spec.2.1]
theorem gap_pos : 0 < 1 - r := sub_pos.mpr r_lt_one

def x (n : ℕ) : ℝ := r ^ n
def b (n : ℕ) : ℝ := 4 * (x n) ^ 2 / (1 - r)
def direction (n : ℕ) : ℝ := -g (x n) / b n
def step (n : ℕ) : ℝ := x (n + 1) - x n
def changeGrad (n : ℕ) : ℝ := g (x (n + 1)) - g (x n)

-- The one-dimensional specialization of the full Hessian BFGS update.
def update (B s y : ℝ) : ℝ := B - (B * s) ^ 2 / (s ^ 2 * B) + y ^ 2 / (y * s)

theorem x_pos (n : ℕ) : 0 < x n := pow_pos r_pos n

theorem x_next (n : ℕ) : x (n + 1) = r * x n := by simp [x, pow_succ, mul_comm]

theorem b_pos (n : ℕ) : 0 < b n := by
  exact div_pos (mul_pos (by norm_num) (sq_pos_of_pos (x_pos n))) gap_pos

theorem search_step (n : ℕ) : x (n + 1) = x n + direction n := by
  rw [x_next]
  dsimp [direction, g, b]
  have hx := ne_of_gt (x_pos n)
  have hg := ne_of_gt gap_pos
  field_simp
  ring

theorem step_formula (n : ℕ) : step n = (r - 1) * x n := by
  rw [step, x_next]; ring

theorem gradient_change (n : ℕ) : changeGrad n = 4 * (r ^ 3 - 1) * (x n) ^ 3 := by
  rw [changeGrad, x_next]; dsimp [g]; ring

theorem step_ne (n : ℕ) : step n ≠ 0 := by
  rw [step_formula]
  exact mul_ne_zero (sub_ne_zero.mpr (ne_of_lt r_lt_one)) (ne_of_gt (x_pos n))

theorem secant_identity (n : ℕ) : changeGrad n = b (n + 1) * step n := by
  rw [gradient_change, step_formula]
  simp only [b, x_next]
  have he := r_spec.2.2
  have hg := ne_of_gt gap_pos
  field_simp
  have he' : (r ^ 3 - 1) * (1 - r) = r ^ 2 * (r - 1) := by
    rw [show r ^ 3 - 1 = -(r ^ 2) by linarith]
    ring
  calc
    _ = 4 * (x n) ^ 3 * ((r ^ 3 - 1) * (1 - r)) := by ring
    _ = 4 * (x n) ^ 3 * (r ^ 2 * (r - 1)) := by rw [he']
    _ = _ := by ring

theorem positive_curvature (n : ℕ) : 0 < changeGrad n * step n := by
  rw [secant_identity]
  rw [mul_assoc, ← pow_two]
  exact mul_pos (b_pos (n + 1)) (sq_pos_of_ne_zero (step_ne n))

theorem update_scalar {B s y : ℝ} (hB : B ≠ 0) (hs : s ≠ 0) (hy : y ≠ 0) :
    update B s y = y / s := by
  dsimp [update]
  field_simp
  ring

theorem bfgs_update (n : ℕ) : b (n + 1) = update (b n) (step n) (changeGrad n) := by
  have hy : changeGrad n ≠ 0 := by
    intro hy
    have h := positive_curvature n
    rw [hy, zero_mul] at h
    exact (lt_irrefl 0) h
  rw [update_scalar (ne_of_gt (b_pos n)) (step_ne n) hy, secant_identity]
  exact (mul_div_cancel_right₀ _ (step_ne n)).symm

-- Unit steps satisfy the standard Armijo and strong Wolfe tests.
theorem armijo (n : ℕ) :
    f (x (n + 1)) ≤ f (x n) + (1 / 100 : ℝ) * g (x n) * direction n := by
  have hd : direction n = (r - 1) * x n := by
    have h := search_step n
    rw [x_next] at h
    linarith
  rw [hd, x_next]
  dsimp [f, g]
  have hr3 : r ^ 3 ≤ 1 := by
    simpa using pow_le_pow_left₀ r_pos.le r_lt_one.le 3
  have hr4 : r ^ 4 ≤ r := by
    nlinarith [mul_le_mul_of_nonneg_left hr3 r_pos.le]
  have hc : r ^ 4 ≤ 1 + (1 / 25 : ℝ) * (r - 1) := by linarith [r_lt_one]
  have hh := mul_le_mul_of_nonneg_right hc (show 0 ≤ (x n) ^ 4 by positivity)
  nlinarith

theorem strong_wolfe (n : ℕ) :
    |g (x (n + 1)) * direction n| ≤ (9 / 10 : ℝ) * |g (x n) * direction n| := by
  have hratio : g (x (n + 1)) * direction n = r ^ 3 * (g (x n) * direction n) := by
    rw [x_next]; dsimp [g]; ring
  rw [hratio, abs_mul, abs_of_pos (pow_pos r_pos 3)]
  have hc : r ^ 3 ≤ (9 / 10 : ℝ) := by
    nlinarith [r_spec.1, r_spec.2.2, sq_nonneg (r - 3 / 4)]
  exact mul_le_mul_of_nonneg_right hc (abs_nonneg _)

theorem descent (n : ℕ) : g (x n) * direction n < 0 := by
  dsimp [direction, g]
  have hg : 0 < 4 * (x n) ^ 3 := mul_pos (by norm_num) (pow_pos (x_pos n) 3)
  exact mul_neg_of_pos_of_neg hg (div_neg_of_neg_of_pos (neg_neg_of_pos hg) (b_pos n))

theorem converges : Tendsto x atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one r_pos.le r_lt_one

def errorRatio (n : ℕ) : ℝ := |x (n + 1) - 0| / |x n - 0|

theorem error_ratio (n : ℕ) : errorRatio n = r := by
  rw [errorRatio, sub_zero, sub_zero, abs_of_pos (x_pos (n + 1)), abs_of_pos (x_pos n), x_next]
  exact mul_div_cancel_right₀ r (ne_of_gt (x_pos n))

theorem not_superlinear : ¬ Tendsto errorRatio atTop (𝓝 0) := by
  intro h
  have hconst : errorRatio = fun _ => r := funext error_ratio
  rw [hconst] at h
  have he : r = 0 := tendsto_nhds_unique tendsto_const_nhds h
  exact (ne_of_gt r_pos) he

#print axioms smooth
#print axioms gradient
#print axioms strict_convex
#print axioms minimizer
#print axioms degenerate_hessian
#print axioms root_exists
#print axioms search_step
#print axioms bfgs_update
#print axioms positive_curvature
#print axioms armijo
#print axioms strong_wolfe
#print axioms descent
#print axioms converges
#print axioms not_superlinear
end BFGS
