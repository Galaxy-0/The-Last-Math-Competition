import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
import Mathlib.MeasureTheory.Measure.Hausdorff

noncomputable section
open scoped RealInnerProductSpace

namespace Conjecture1561

abbrev Space := EuclideanSpace ℝ (Fin 3)

/-- The actual unit sphere in three-dimensional Euclidean space. -/
def sphereS2 : Set Space := Metric.sphere 0 1

/-- On unit vectors this is the usual great-circle distance in radians. -/
def sphericalDistance (x y : Space) : ℝ := InnerProductGeometry.angle x y

def closedHemisphere (v : Space) : Set Space :=
  {x | x ∈ sphereS2 ∧ 0 ≤ @inner ℝ Space _ v x}

def openHemisphere (v : Space) : Set Space :=
  {x | x ∈ sphereS2 ∧ 0 < @inner ℝ Space _ v x}

/-- The exact pairwise spherical-distance constraint in the source. -/
def Admissible (A : Set Space) : Prop :=
  A ⊆ sphereS2 ∧ ∀ x ∈ A, ∀ y ∈ A, sphericalDistance x y ≤ Real.pi / 2

/-- A maximizer must itself satisfy the constraint it optimizes over. -/
def IsAreaMaximizer (μ : MeasureTheory.Measure Space) (A : Set Space) : Prop :=
  Admissible A ∧ ∀ B : Set Space, Admissible B → μ B ≤ μ A

/-- Actual two-dimensional Hausdorff measure; its normalization will not matter. -/
def sphericalArea : MeasureTheory.Measure Space :=
  MeasureTheory.Measure.hausdorffMeasure 2

def HemisphereExtremizerClaim (μ : MeasureTheory.Measure Space) : Prop :=
  ∃ v ∈ sphereS2, IsAreaMaximizer μ (closedHemisphere v)

/-- The first asserted extremizer, a necessary clause of the full conjecture. -/
def ConjectureFirstClause : Prop := HemisphereExtremizerClaim sphericalArea

end Conjecture1561
