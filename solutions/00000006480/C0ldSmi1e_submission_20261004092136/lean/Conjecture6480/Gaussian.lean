import Mathlib.Probability.Distributions.Gaussian
import Mathlib.Tactic

/-! A genuine Gaussian-law obstruction from an atom of intermediate mass. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Conjecture6480

/-- A real Gaussian law has no atoms unless its variance is zero; then it is a point mass. -/
theorem gaussianReal_singleton_zero_or_one (a : ℝ) (v : ℝ≥0) (x : ℝ) :
    gaussianReal a v {x} = 0 ∨ gaussianReal a v {x} = 1 := by
  by_cases hv : v = 0
  · rw [hv, gaussianReal_zero_var]
    by_cases ha : a = x
    · right
      simp [ha]
    · left
      simp [Measure.dirac_apply, ha]
  · left
    exact (gaussianReal_absolutelyContinuous a hv) (by simp)

/-- A measure with an atom whose mass is neither zero nor one is no real Gaussian law,
including the degenerate variance-zero Gaussian laws. -/
theorem not_gaussianReal_of_intermediate_atom (ν : Measure ℝ) (x : ℝ)
    (hzero : ν {x} ≠ 0) (hone : ν {x} ≠ 1) (a : ℝ) (v : ℝ≥0) :
    ν ≠ gaussianReal a v := by
  intro hν
  rcases gaussianReal_singleton_zero_or_one a v x with h | h
  · exact hzero (hν ▸ h)
  · exact hone (hν ▸ h)

/-- In particular, an atom of mass one-half excludes every Gaussian law. -/
theorem not_gaussianReal_of_half_atom (ν : Measure ℝ) (x : ℝ)
    (hhalf : ν {x} = (1 / 2 : ℝ≥0∞)) (a : ℝ) (v : ℝ≥0) :
    ν ≠ gaussianReal a v := by
  apply not_gaussianReal_of_intermediate_atom ν x
  · rw [hhalf]
    norm_num
  · rw [hhalf]
    norm_num

/-- For a process on three indices, Gaussianity means that every real linear combination
of its coordinates has an actual real Gaussian law, allowing zero variance. -/
def GaussianProcess {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Z : Fin 3 → Ω → ℝ) : Prop :=
  ∀ c : Fin 3 → ℝ, ∃ a : ℝ, ∃ v : ℝ≥0,
    Measure.map (fun ω ↦ ∑ i, c i * Z i ω) μ = gaussianReal a v

/-- Selecting a single coefficient shows that every coordinate of a Gaussian process is Gaussian. -/
theorem GaussianProcess.coordinate {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {Z : Fin 3 → Ω → ℝ} (hG : GaussianProcess μ Z) (i : Fin 3) :
    ∃ a : ℝ, ∃ v : ℝ≥0, Measure.map (Z i) μ = gaussianReal a v := by
  obtain ⟨a, v, h⟩ := hG (fun j ↦ if j = i then 1 else 0)
  refine ⟨a, v, ?_⟩
  simpa using h

/-- An intermediate atom in any coordinate rules out the standard Gaussian-process property. -/
theorem not_gaussianProcess_of_half_atom {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Z : Fin 3 → Ω → ℝ) (i : Fin 3) (x : ℝ)
    (hhalf : (Measure.map (Z i) μ) {x} = (1 / 2 : ℝ≥0∞)) :
    ¬ GaussianProcess μ Z := by
  intro hG
  obtain ⟨a, v, h⟩ := hG.coordinate i
  exact not_gaussianReal_of_half_atom _ x hhalf a v h

/-- The first-coordinate specialization used by the concrete processes. -/
theorem not_gaussianProcess_of_coordinate_zero_half_atom {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Z : Fin 3 → Ω → ℝ) (x : ℝ)
    (hhalf : (Measure.map (Z 0) μ) {x} = (1 / 2 : ℝ≥0∞)) :
    ¬ GaussianProcess μ Z :=
  not_gaussianProcess_of_half_atom μ Z 0 x hhalf

end Conjecture6480
