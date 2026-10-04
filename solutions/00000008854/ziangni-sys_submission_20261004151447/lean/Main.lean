import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

open Filter
open scoped Topology
noncomputable section
namespace MetricGradient

def metric : ℝ →L[ℝ] ℝ := ContinuousLinearMap.id ℝ ℝ
def metricMatrix : Matrix (Fin 1) (Fin 1) ℝ := 1
def spectralSet : Set ℝ := {eig | ∃ v : ℝ, v ≠ 0 ∧ metric v = eig * v}

theorem matrix_representation (x : Fin 1 → ℝ) :
    metricMatrix.mulVec x 0 = metric (x 0) := by
  simp [metricMatrix, metric]

theorem metric_inverse (x : ℝ) : metric (metric x) = x := by simp [metric]

theorem metric_positive (x : ℝ) (h : x ≠ 0) : 0 < x * metric x := by
  simpa [metric, pow_two] using sq_pos_of_ne_zero h

theorem actual_spectrum : spectralSet = {1} := by
  ext eig
  constructor
  · rintro ⟨v, hv, he⟩
    simp [metric] at he
    have : eig = 1 := mul_right_cancel₀ hv (by simpa using he.symm)
    simpa using this
  · intro h
    simp only [Set.mem_singleton_iff] at h
    subst eig
    exact ⟨1, by norm_num, by simp [metric]⟩

def midpoint : ℝ := (1 + 1) / 2
theorem midpoint_value : midpoint = 1 := by norm_num [midpoint]

def metricDistanceSq (x y : ℝ) : ℝ := (x-y) * metric (x-y)
def projection (y : ℝ) : ℝ := y
def IsMetricProjection (y p : ℝ) : Prop :=
  p ∈ (Set.univ : Set ℝ) ∧ ∀ z : ℝ, metricDistanceSq p y ≤ metricDistanceSq z y

theorem actual_projection (y : ℝ) : IsMetricProjection y (projection y) := by
  refine ⟨Set.mem_univ _, ?_⟩
  intro z
  simpa [metricDistanceSq, metric, projection, pow_two] using sq_nonneg (z-y)

theorem projection_unique (y p : ℝ) (h : IsMetricProjection y p) : p = y := by
  have hp := h.2 y
  simp [metricDistanceSq, metric] at hp
  nlinarith [sq_nonneg (p-y)]

def objective (x : ℝ) : ℝ := 2*x^2

theorem actual_derivative (x : ℝ) : HasDerivAt objective (4*x) x := by
  convert ((hasDerivAt_id x).pow 2).const_mul 2 using 1 <;> simp [objective] <;> ring

theorem actual_gradient (x : ℝ) : HasGradientAt objective (4*x) x :=
  (actual_derivative x).hasGradientAt'

theorem gradient_value (x : ℝ) : gradient objective x = 4*x :=
  (actual_gradient x).gradient

theorem strong_quadratic_identity (x y : ℝ) :
    objective y = objective x + gradient objective x * (y-x) + 2*(y-x)^2 := by
  rw [gradient_value]; unfold objective; ring

theorem unique_minimum (p : ℝ) :
    (∀ x, objective p ≤ objective x) ↔ p = 0 := by
  constructor
  · intro h
    have hp := h 0
    simp [objective] at hp
    nlinarith [sq_nonneg p]
  · rintro rfl
    intro x
    simp only [objective, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero]
    positivity

def step (η x : ℝ) : ℝ := projection (x - η * metric (gradient objective x))

theorem step_formula (η x : ℝ) : step η x = (1-4*η)*x := by
  simp [step, projection, metric, gradient_value]; ring

def orbit (η : ℝ) : ℕ → ℝ
  | 0 => 1
  | n+1 => step η (orbit η n)

theorem actual_iterates (η : ℝ) (n : ℕ) : orbit η n = (1-4*η)^n := by
  induction n with
  | zero => simp [orbit]
  | succ n ih => rw [orbit, step_formula, ih, pow_succ]; ring

theorem midpoint_error (n : ℕ) : |orbit midpoint n| = (3 : ℝ)^n := by
  rw [actual_iterates, midpoint_value, abs_pow]
  norm_num

theorem midpoint_escape : Tendsto (fun n => |orbit midpoint n|) atTop atTop := by
  simpa only [midpoint_error] using
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 3))

theorem quarter_termination (n : ℕ) : orbit (1/4) (n+1) = 0 := by
  rw [actual_iterates]
  norm_num

def contractionFactor (η : ℝ) : ℝ := |step η 1|

theorem factor_formula (η : ℝ) : contractionFactor η = |1-4*η| := by
  simp [contractionFactor, step_formula]

theorem actual_error_factor (η x : ℝ) : |step η x| = contractionFactor η * |x| := by
  rw [step_formula, factor_formula, abs_mul]

theorem unique_optimal_step (η : ℝ) :
    (∀ ζ : ℝ, contractionFactor η ≤ contractionFactor ζ) ↔ η = 1/4 := by
  constructor
  · intro h
    have hh := h (1/4)
    rw [factor_formula, factor_formula] at hh
    norm_num at hh
    linarith
  · rintro rfl
    intro ζ
    rw [factor_formula, factor_formula]
    norm_num

theorem midpoint_not_optimal :
    ¬ (∀ ζ : ℝ, contractionFactor midpoint ≤ contractionFactor ζ) := by
  rw [unique_optimal_step, midpoint_value]
  norm_num

theorem counterexample :
    spectralSet = {1} ∧ midpoint = 1 ∧
    (∀ y, IsMetricProjection y (projection y)) ∧
    (∀ x, HasGradientAt objective (4*x) x) ∧
    (∀ n, orbit (1/4) (n+1) = 0) ∧
    Tendsto (fun n => |orbit midpoint n|) atTop atTop ∧
    ¬ (∀ ζ : ℝ, contractionFactor midpoint ≤ contractionFactor ζ) :=
  ⟨actual_spectrum, midpoint_value, actual_projection, actual_gradient,
    quarter_termination, midpoint_escape, midpoint_not_optimal⟩

#print axioms actual_spectrum
#print axioms actual_projection
#print axioms actual_gradient
#print axioms unique_minimum
#print axioms actual_iterates
#print axioms midpoint_escape
#print axioms unique_optimal_step
#print axioms counterexample
end MetricGradient
