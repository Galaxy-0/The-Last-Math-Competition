import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Conjecture308

/-- The standard Gaussian-rational badly approximable set. Division is in C. -/
def BadC : Set ℂ := {z | ∃ c : ℝ, 0 < c ∧
  ∀ p q : GaussianInt, q ≠ 0 →
    c / ‖(q : ℂ)‖ ^ 2 ≤ ‖z - (p : ℂ) / (q : ℂ)‖}

/-- A real affine line in the complex plane, when its direction is nonzero. -/
def realLine (a v : ℂ) : Set ℂ := {z | ∃ t : ℝ, z = a + (t : ℂ) * v}

/-- The real axis is the line through zero in direction one. -/
def realAxis : Set ℂ := realLine 0 1

end Conjecture308
