import Mathlib.Probability.Distributions.Exponential
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section
open MeasureTheory ProbabilityTheory Real Set

namespace Conjecture7790

/-- The law of a rate-one exponential random variable minus its mean. -/
def centeredExponential : Measure ℝ :=
  (expMeasure 1).map (fun y : ℝ => y - 1)

/-- Its density with respect to real Lebesgue measure. -/
def density (x : ℝ) : ℝ :=
  if -1 ≤ x then Real.exp (-(x + 1)) else 0

/-- The full weighted geometric-mean definition, including zero-density points. -/
def IsLogConcaveDensity (f : ℝ → ℝ) : Prop :=
  (∀ x, 0 ≤ f x) ∧
    ∀ x y a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      f x ^ a * f y ^ b ≤ f (a * x + b * y)

/-- In one real dimension, isotropy is zero mean and unit second moment. -/
def IsIsotropic (μ : Measure ℝ) : Prop :=
  Integrable (fun x : ℝ => x) μ ∧
  Integrable (fun x : ℝ => x ^ 2) μ ∧
  (∫ x : ℝ, x ∂μ) = 0 ∧ (∫ x : ℝ, x ^ 2 ∂μ) = 1

end Conjecture7790
