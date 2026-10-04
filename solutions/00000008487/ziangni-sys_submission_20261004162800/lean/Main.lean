import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.GDelta.Basic
import Mathlib.Topology.Instances.Real.Lemmas

noncomputable section
namespace DenseComplementContradiction

/-- No subset of a nonempty topological space satisfies the two source claims. -/
theorem no_dense_open_complement {X : Type*} [TopologicalSpace X] [Nonempty X]
    (s : Set X) : ¬ (Dense s ∧ IsOpen sᶜ ∧ Dense sᶜ) := by
  rintro ⟨hs, ho, hc⟩
  obtain ⟨x, hxc, hxs⟩ := hs.inter_open_nonempty sᶜ ho hc.nonempty
  exact hxc hxs

abbrev Interval := Set.Icc (0 : ℝ) 1
abbrev Observables := C(Interval, ℝ)

/-- Actual interval observables form a nonempty space: the zero observable exists. -/
theorem observables_nonempty : Nonempty Observables := ⟨0⟩

/-- The complete topology conjunction asserted in the source. -/
def ClaimedTopology (locked : Set Observables) : Prop :=
  Dense locked ∧ IsGδ locked ∧ IsOpen lockedᶜ ∧ Dense lockedᶜ

/-- This applies to the actual locking set for every interval dynamical map,
regardless of the precise locking convention. -/
theorem interval_claim_impossible (locked : Set Observables) : ¬ ClaimedTopology locked := by
  rintro ⟨hd, _, ho, hc⟩
  exact no_dense_open_complement locked ⟨hd, ho, hc⟩

/-- Even allowing any candidate locking set cannot repair the asserted conjunction. -/
theorem counterexample : ¬ ∃ locked : Set Observables, ClaimedTopology locked := by
  rintro ⟨locked, h⟩
  exact interval_claim_impossible locked h
end DenseComplementContradiction
end
#print axioms DenseComplementContradiction.no_dense_open_complement
#print axioms DenseComplementContradiction.observables_nonempty
#print axioms DenseComplementContradiction.interval_claim_impossible
#print axioms DenseComplementContradiction.counterexample
