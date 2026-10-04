import Probability

namespace Conjecture420
open MeasureTheory Filter
open scoped Topology

/-- The proposed density is not a probability law and is not the weak limit of any
sequence of probability laws. In particular, it cannot be the angular limit law
asserted in conjecture 00000000420. -/
theorem conjecture420_disproof :
    (¬ IsProbabilityMeasure candidateMeasure) ∧
    ∀ μ : ℕ → ProbabilityMeasure ℝ,
      ¬ Tendsto (fun n ↦ (μ n).toFiniteMeasure) atTop (𝓝 candidateFiniteMeasure) := by
  exact ⟨candidateMeasure_not_probability, no_probability_sequence_weak_limit⟩

end Conjecture420
