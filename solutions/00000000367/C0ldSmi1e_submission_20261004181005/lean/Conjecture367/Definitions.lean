import Mathlib.Algebra.LinearRecurrence
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.GroupTheory.OrderOfElement

noncomputable section
open scoped Topology

namespace Conjecture367

/-- A family with two genuine exponential summands. -/
def sequence (r : ℝ) (n : ℕ) : ℝ := 2 ^ n + r ^ n

/-- The actual second-order recurrence satisfied by the family. -/
def recurrence (r : ℝ) : LinearRecurrence ℝ :=
  ⟨2, ![-2 * r, 2 + r]⟩

/-- Nonzero complex characteristic roots, with no root-of-unity quotient
between distinct roots. -/
def Nondegenerate (R : LinearRecurrence ℝ) : Prop :=
  (∀ a : ℂ, (R.charPoly.map Complex.ofRealHom).IsRoot a → a ≠ 0) ∧
  ∀ a b : ℂ, (R.charPoly.map Complex.ofRealHom).IsRoot a →
    (R.charPoly.map Complex.ofRealHom).IsRoot b → a ≠ b → ¬ IsOfFinOrder (a / b)

/-- The recurrence has the true minimal order of the sequence. -/
def IsMinimalRecurrence (R : LinearRecurrence ℝ) (u : ℕ → ℝ) : Prop :=
  R.IsSolution u ∧ ∀ S : LinearRecurrence ℝ, S.IsSolution u → R.order ≤ S.order

/-- Distance to the actual set of all integers. -/
def distanceToIntegers (x : ℝ) : ℝ :=
  Metric.infDist x (Set.range (Int.cast : ℤ → ℝ))

/-- Even an eventual bound would be necessary for the stated pointwise claim. -/
def HasPolynomialLowerBound (u : ℕ → ℝ) : Prop :=
  ∃ C : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 0 < n →
    (n : ℝ) ^ (-C) < distanceToIntegers (u n)

/-- The existence assertion needed before an explicit root-gap formula for C. -/
def ClaimedLowerBound : Prop :=
  ∀ (R : LinearRecurrence ℝ) (u : ℕ → ℝ), 0 < R.order →
    IsMinimalRecurrence R u → Nondegenerate R → HasPolynomialLowerBound u

end Conjecture367
