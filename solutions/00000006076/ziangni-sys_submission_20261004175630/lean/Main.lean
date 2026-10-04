import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section
open Filter
open scoped Topology
namespace SaddleEscape
abbrev E := EuclideanSpace ℝ (Fin 2)
def f (x : E) : ℝ := (x 0)^2 - (x 1)^2
def coord (j : Fin 2) : E →L[ℝ] ℝ := EuclideanSpace.proj j
def e (j : Fin 2) (s : ℝ) : E := EuclideanSpace.single j s
def H : E →L[ℝ] E :=
  (coord 0).smulRight (e 0 2) + (coord 1).smulRight (e 1 (-2))

theorem H_coordinates (x : E) : H x 0 = 2*x 0 ∧ H x 1 = -2*x 1 := by
  simp [H, coord, e, EuclideanSpace.single_apply, mul_comm]

theorem actual_gradient (x : E) : HasGradientAt f (H x) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hx := (coord 0).hasFDerivAt (x := x)
  have hy := (coord 1).hasFDerivAt (x := x)
  convert (hx.mul hx).sub (hy.mul hy) using 1
  · ext z
    simp [f, coord, pow_two]
  · ext z
    simp [InnerProductSpace.toDual_apply, H, coord, e, inner_add_left,
      real_inner_smul_left, EuclideanSpace.inner_single_left]
    ring

theorem gradient_formula (x : E) : gradient f x = H x := (actual_gradient x).gradient
theorem smooth : ContDiff ℝ ⊤ f := by
  unfold f
  simpa [coord, pow_two] using
    (((coord 0).contDiff.mul (coord 0).contDiff).sub
      ((coord 1).contDiff.mul (coord 1).contDiff))
theorem actual_hessian (x : E) : HasFDerivAt (gradient f) H x := by
  have h : gradient f = H := funext gradient_formula
  rw [h]
  exact H.hasFDerivAt
theorem stationary : gradient f 0 = 0 := by simp [gradient_formula]

theorem nondegenerate (x : E) (h : H x = 0) : x = 0 := by
  have h0 := congrArg (fun y : E => y 0) h
  have h1 := congrArg (fun y : E => y 1) h
  change H x 0 = 0 at h0
  change H x 1 = 0 at h1
  rw [(H_coordinates x).1] at h0
  rw [(H_coordinates x).2] at h1
  ext j
  fin_cases j <;> simp_all

theorem negative_curvature : @inner ℝ E _ (e 1 1) (H (e 1 1)) = -2 := by
  simp [H, coord, e, inner_add_right, real_inner_smul_right,
    EuclideanSpace.inner_single_left, EuclideanSpace.single_apply]
theorem positive_curvature : @inner ℝ E _ (e 0 1) (H (e 0 1)) = 2 := by
  simp [H, coord, e, inner_add_right, real_inner_smul_right,
    EuclideanSpace.inner_single_left, EuclideanSpace.single_apply]

theorem axis_norm (j : Fin 2) (s : ℝ) : ‖e j s‖ = |s| := by
  simp [e, Real.norm_eq_abs]
theorem axis_objective (s : ℝ) : f (e 0 s) = s^2 ∧ f (e 1 s) = -s^2 := by
  simp [f, e, EuclideanSpace.single_apply]

theorem strict_saddle_not_min_or_max : ¬ IsLocalMin f 0 ∧ ¬ IsLocalMax f 0 := by
  constructor
  · intro h
    rcases Metric.mem_nhds_iff.mp h with ⟨r, hr, hb⟩
    have hm : e 1 (r/2) ∈ Metric.ball (0 : E) r := by
      rw [Metric.mem_ball, dist_zero_right, axis_norm, abs_of_pos (by linarith)]
      linarith
    have hh := hb hm
    simp [f, e, EuclideanSpace.single_apply] at hh
    have hp : 0 < (r/2)^2 := sq_pos_of_pos (by linarith)
    linarith
  · intro h
    rcases Metric.mem_nhds_iff.mp h with ⟨r, hr, hb⟩
    have hm : e 0 (r/2) ∈ Metric.ball (0 : E) r := by
      rw [Metric.mem_ball, dist_zero_right, axis_norm, abs_of_pos (by linarith)]
      linarith
    have hh := hb hm
    simp [f, e, EuclideanSpace.single_apply] at hh
    have hp : 0 < (r/2)^2 := sq_pos_of_pos (by linarith)
    linarith

def step (x : E) : E := x - (1/4 : ℝ) • gradient f x
def trajectory (s : ℝ) (n : ℕ) : E := e 0 (s*(1/2 : ℝ)^n)
theorem safe_step : 0 < (1/4 : ℝ) ∧ (1/4 : ℝ) < 1/2 := by norm_num
theorem actual_initial (s : ℝ) : trajectory s 0 = e 0 s := by simp [trajectory]
theorem actual_update (s : ℝ) (n : ℕ) : step (trajectory s n) = trajectory s (n+1) := by
  ext j
  fin_cases j <;>
    simp [step, gradient_formula, H, coord, trajectory, e, EuclideanSpace.single_apply,
      pow_succ] <;> ring
theorem actual_iterates (s : ℝ) (n : ℕ) : step^[n] (e 0 s) = trajectory s n := by
  induction n with
  | zero => simp [actual_initial]
  | succ n hn => rw [Function.iterate_succ_apply', hn, actual_update]

theorem nonstationary_start {s : ℝ} (hs : 0 < s) : gradient f (e 0 s) ≠ 0 := by
  intro h
  have hz := congrArg (fun y : E => y 0) h
  simp [gradient_formula, H, coord, e, EuclideanSpace.single_apply] at hz
  linarith

theorem never_escapes {r s : ℝ} (hs : 0 < s) (hsr : s < r) (n : ℕ) :
    step^[n] (e 0 s) ∈ Metric.ball (0 : E) r := by
  rw [actual_iterates, Metric.mem_ball, dist_zero_right]
  rw [trajectory, axis_norm, abs_of_pos (mul_pos hs (pow_pos (by norm_num) _))]
  have hp : (1/2 : ℝ)^n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hm : s*(1/2 : ℝ)^n ≤ s := by nlinarith
  exact lt_of_le_of_lt hm hsr

theorem converges_to_saddle (s : ℝ) :
    Tendsto (fun n => step^[n] (e 0 s)) atTop (𝓝 (0 : E)) := by
  simp_rw [actual_iterates]
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp only [sub_zero, trajectory, axis_norm]
  have h := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2)
    (by norm_num : (1/2 : ℝ) < 1)
  simpa using (tendsto_const_nhds.mul h).abs

theorem counterexample (r : ℝ) (hr : 0 < r) :
    ∃ x : E, x ∈ Metric.ball (0 : E) r ∧ gradient f x ≠ 0 ∧
      (∀ n : ℕ, step^[n] x ∈ Metric.ball (0 : E) r) ∧
      Tendsto (fun n => step^[n] x) atTop (𝓝 (0 : E)) := by
  refine ⟨e 0 (r/2), ?_, nonstationary_start (by linarith), ?_, converges_to_saddle _⟩
  · simpa using never_escapes (by linarith : 0 < r/2) (by linarith : r/2 < r) 0
  · exact never_escapes (by linarith) (by linarith)

#print axioms actual_gradient
#print axioms smooth
#print axioms actual_hessian
#print axioms stationary
#print axioms nondegenerate
#print axioms negative_curvature
#print axioms positive_curvature
#print axioms strict_saddle_not_min_or_max
#print axioms actual_iterates
#print axioms nonstationary_start
#print axioms never_escapes
#print axioms converges_to_saddle
#print axioms counterexample
end SaddleEscape
