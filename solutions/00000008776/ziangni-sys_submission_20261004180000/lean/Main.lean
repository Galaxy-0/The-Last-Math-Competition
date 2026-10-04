import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

open MeasureTheory Filter
open scoped Topology ENNReal
noncomputable section
namespace SamplingCounterexample
abbrev Row := Fin 2
instance : MeasurableSpace Row := ⊤
instance : MeasurableSingletonClass Row := ⟨fun _ => trivial⟩

def A : Matrix Row (Fin 1) ℝ := fun _ _ => 1
def b : Row → ℝ := fun _ => 0
def residual (i : Row) (x : ℝ) : ℝ := A i 0 * x - b i

theorem overdetermined : Fintype.card (Fin 1) < Fintype.card Row := by decide
theorem rows_nonzero (i : Row) : A i 0 ≠ 0 := by norm_num [A]
theorem consistent : ∀ i, residual i 0 = 0 := by simp [residual, A, b]

def rowLoss (i : Row) (x : ℝ) : ℝ := (residual i x)^2/2
def loss (x : ℝ) : ℝ := (∑ i : Row, rowLoss i x)/2

theorem loss_formula (x : ℝ) : loss x = x^2/2 := by
  simp [loss, rowLoss, residual, A, b, Fin.sum_univ_two]

theorem actual_gradient (i : Row) (x : ℝ) : gradient (rowLoss i) x = x := by
  have hf : rowLoss i = (fun y : ℝ => y^2/2) := by
    funext y
    simp [rowLoss, residual, A, b]
  rw [hf]
  convert (((hasDerivAt_id x).pow 2).div_const 2).hasGradientAt'.gradient using 1 <;> norm_num <;> ring
theorem unique_minimum (x : ℝ) : (∀ y, loss x ≤ loss y) ↔ x=0 := by
  constructor
  · intro h
    have hh := h 0
    rw [loss_formula, loss_formula] at hh
    have := sq_nonneg x
    nlinarith
  · rintro rfl
    intro y
    rw [loss_formula, loss_formula]
    nlinarith [sq_nonneg y]

-- The mean normal-equation matrix is scalar 1, and its actual inverse is 1.
def meanGram : ℝ := (∑ i : Row, (A i 0)^2)/2
def diagonalPreconditioner : ℝ := meanGram⁻¹
theorem actual_preconditioner : meanGram=1 ∧ diagonalPreconditioner=1 ∧
    diagonalPreconditioner * meanGram=1 := by
  norm_num [meanGram, diagonalPreconditioner, A, Fin.sum_univ_two]

def score (i : Row) (x : ℝ) : ℝ := (diagonalPreconditioner * residual i x)^2

theorem normalized_score (x : ℝ) (hx : x≠0) (i : Row) :
    score i x / (∑ j : Row, score j x) = 1/2 := by
  simp [score, actual_preconditioner.2.1, residual, A, b, Fin.sum_univ_two]
  field_simp
  ring

lemma ofReal_half : ENNReal.ofReal (1/2 : ℝ) = (1/2 : ℝ≥0∞) := by
  rw [ENNReal.ofReal_div_of_pos (by norm_num)]
  norm_num
def uniform : PMF Row := PMF.ofFintype (fun _ => (1/2 : ℝ≥0∞)) (by
  norm_num [Fin.sum_univ_two, ← ENNReal.add_div]
  exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num))

def residualLaw (x : ℝ) : PMF Row :=
  if hx : x=0 then uniform else
  PMF.ofFintype (fun i => ENNReal.ofReal (score i x/(∑ j : Row, score j x))) (by
    simp only [normalized_score x hx, ofReal_half]
    norm_num [Fin.sum_univ_two, ← ENNReal.add_div]
    exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num))

theorem residual_law_uniform (x : ℝ) : residualLaw x = uniform := by
  by_cases hx : x=0
  · simp [residualLaw, hx]
  · ext i
    simp only [residualLaw, dif_neg hx, uniform, PMF.ofFintype_apply]
    rw [normalized_score x hx i]
    exact ofReal_half

-- A genuine SGD update of the actual row loss, with safe step 1/2.
def update (i : Row) (x : ℝ) : ℝ :=
  x - (1/2:ℝ)*diagonalPreconditioner*gradient (rowLoss i) x

theorem update_formula (i : Row) (x : ℝ) : update i x = x/2 := by
  rw [update, actual_gradient, actual_preconditioner.2.1]
  ring

-- Every sampling distribution is variance-optimal here: sample gradients agree.
theorem gradient_sampling_variance (p : PMF Row) (x : ℝ) :
    (∫ i, (gradient (rowLoss i) x - x)^2 ∂p.toMeasure)=0 := by
  simp [actual_gradient]

def kernel (R : ℝ → PMF Row) (x : ℝ) : PMF ℝ :=
  (R x).bind (fun i => PMF.pure (update i x))

theorem kernel_deterministic (R : ℝ → PMF Row) (x : ℝ) :
    kernel R x = PMF.pure (x/2) := by
  simp only [kernel, update_formula]
  exact PMF.bind_const _ _

def evolve (R : ℝ → PMF Row) : ℕ → PMF ℝ → PMF ℝ
  | 0, p => p
  | n+1, p => (evolve R n p).bind (kernel R)

theorem actual_law (R : ℝ → PMF Row) (n : ℕ) :
    evolve R n (PMF.pure 1) = PMF.pure ((1/2:ℝ)^n) := by
  induction n with
  | zero => simp [evolve]
  | succ n ih =>
    rw [evolve, ih, PMF.pure_bind, kernel_deterministic]
    congr 1
    rw [pow_succ]
    ring

theorem all_states_positive (n : ℕ) : 0 < (1/2:ℝ)^n := pow_pos (by norm_num) n

theorem actual_expected_error (R : ℝ → PMF Row) (n : ℕ) :
    (∫ x : ℝ, ‖x‖ ∂(evolve R n (PMF.pure 1)).toMeasure) = (1/2:ℝ)^n := by
  rw [actual_law, PMF.toMeasure_pure]
  simp [Real.norm_eq_abs, abs_of_pos (all_states_positive n)]

theorem convergence : Tendsto (fun n : ℕ => (1/2:ℝ)^n) atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

theorem identical_full_laws (n : ℕ) :
    evolve residualLaw n (PMF.pure 1) = evolve (fun _ => uniform) n (PMF.pure 1) := by
  rw [actual_law, actual_law]

theorem no_strict_improvement (n : ℕ) : ¬
    (∫ x : ℝ, ‖x‖ ∂(evolve residualLaw n (PMF.pure 1)).toMeasure) <
    (∫ x : ℝ, ‖x‖ ∂(evolve (fun _ => uniform) n (PMF.pure 1)).toMeasure) := by
  rw [identical_full_laws]
  exact lt_irrefl _
end SamplingCounterexample
end
#print axioms SamplingCounterexample.actual_gradient
#print axioms SamplingCounterexample.normalized_score
#print axioms SamplingCounterexample.residual_law_uniform
#print axioms SamplingCounterexample.gradient_sampling_variance
#print axioms SamplingCounterexample.actual_law
#print axioms SamplingCounterexample.actual_expected_error
#print axioms SamplingCounterexample.no_strict_improvement
