import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.WithDensity

namespace Conjecture420
open MeasureTheory

noncomputable def leftEndpoint : ℝ := -Real.pi / 2
noncomputable def rightEndpoint : ℝ := Real.pi / 2

def angularInterval : Set ℝ := Set.Icc leftEndpoint rightEndpoint

/-- The exact proposed density, with respect to Lebesgue measure in the angle. -/
noncomputable def rho (x : ℝ) : ℝ :=
  (2 / Real.pi) * Real.cos x * Real.sqrt (1 - Real.sin x)

/-- The measure specified by the conjecture's formula and angular support. -/
noncomputable def candidateMeasure : Measure ℝ :=
  (volume.restrict angularInterval).withDensity (fun x ↦ ENNReal.ofReal (rho x))

end Conjecture420
