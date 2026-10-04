import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Tactic

noncomputable section
namespace LockingCounterexample
open MeasureTheory
open scoped ENNReal
abbrev Ω := Unit
instance : MeasurableSpace Ω := borel Ω
instance : BorelSpace Ω := ⟨rfl⟩
def T : Ω → Ω := id
abbrev Observables := C(Ω, ℝ)

theorem compact_system : CompactSpace Ω := inferInstance
theorem continuous_dynamics : Continuous T := continuous_id

theorem probability_unique (μ : Measure Ω) [IsProbabilityMeasure μ] :
    μ = Measure.dirac () := by
  apply Measure.ext_of_singleton
  intro x
  have hx : ({x} : Set Ω) = Set.univ := by ext y; simp [Subsingleton.elim y x]
  rw [hx]
  simp

theorem invariant : MeasurePreserving T (Measure.dirac ()) (Measure.dirac ()) := MeasurePreserving.id _

def Maximizing (f : Observables) (μ : Measure Ω) : Prop :=
  IsProbabilityMeasure μ ∧ MeasurePreserving T μ μ ∧
  ∀ ν : Measure Ω, IsProbabilityMeasure ν → MeasurePreserving T ν ν →
    (∫ x, f x ∂ν) ≤ ∫ x, f x ∂μ

theorem dirac_maximizing (f : Observables) : Maximizing f (Measure.dirac ()) := by
  refine ⟨inferInstance, invariant, ?_⟩
  intro ν hν _
  letI := hν
  rw [probability_unique ν]

theorem maximizing_iff (f : Observables) (μ : Measure Ω) :
    Maximizing f μ ↔ μ = Measure.dirac () := by
  constructor
  · intro h
    letI := h.1
    exact probability_unique μ
  · rintro rfl
    exact dirac_maximizing f

theorem actual_integral (f : Observables) : (∫ x, f x ∂Measure.dirac ()) = f () := by simp

/-- The actual uniform measure on the length-one orbit, with its averaging weight. -/
def orbitMeasure (x : Ω) : Measure Ω :=
  (1 : ℝ≥0∞)⁻¹ • ∑ i : Fin 1, Measure.dirac ((T^[i.val]) x)

theorem orbit_measure (x : Ω) : orbitMeasure x = Measure.dirac () := by
  cases x
  simp [orbitMeasure]

theorem periodic (x : Ω) : Function.IsPeriodicPt T 1 x := by
  simp [Function.IsPeriodicPt, Function.IsFixedPt, T]

/-- The source's finite-periodic-orbit definition of locking. -/
def Locked (f : Observables) : Prop :=
  ∃ s : Finset Ω, s.Nonempty ∧
    (∀ x ∈ s, Function.IsPeriodicPt T 1 x) ∧
    ∀ μ : Measure Ω, Maximizing f μ ↔ ∃ x ∈ s, μ = orbitMeasure x

theorem all_locked (f : Observables) : Locked f := by
  refine ⟨{()}, by simp, ?_, ?_⟩
  · intro x _
    exact periodic x
  · intro μ
    simp [maximizing_iff, orbit_measure]

def lockedFunctions : Set Observables := {f | Locked f}

theorem locked_full : lockedFunctions = Set.univ := by
  ext f
  simp [lockedFunctions, all_locked]

theorem complement_empty : lockedFunctionsᶜ = ∅ := by rw [locked_full]; simp

theorem complement_not_dense : ¬ Dense lockedFunctionsᶜ := by
  rw [complement_empty]
  intro h
  simpa using h.nonempty

theorem counterexample : (∀ f : Observables, Locked f) ∧ ¬ Dense lockedFunctionsᶜ :=
  ⟨all_locked, complement_not_dense⟩
end LockingCounterexample
end
#print axioms LockingCounterexample.probability_unique
#print axioms LockingCounterexample.maximizing_iff
#print axioms LockingCounterexample.actual_integral
#print axioms LockingCounterexample.orbit_measure
#print axioms LockingCounterexample.all_locked
#print axioms LockingCounterexample.counterexample
