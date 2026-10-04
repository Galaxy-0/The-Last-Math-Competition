import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Tactic

noncomputable section
namespace ParetoCounterexample
open MeasureTheory Filter

abbrev Ω := Fin 2
instance : MeasurableSpace Ω := borel Ω
instance : BorelSpace Ω := ⟨rfl⟩
def T : Ω → Ω := id
def f (i : Ω) : ℝ := if i = 0 then 1 else 0
def g (i : Ω) : ℝ := 1 - f i

theorem compact_system : CompactSpace Ω := inferInstance
theorem continuous_map : Continuous T := continuous_id
theorem continuous_observables : Continuous f ∧ Continuous g :=
  ⟨continuous_of_discreteTopology, continuous_of_discreteTopology⟩

theorem dirac_ergodic (a : Ω) : Ergodic T (Measure.dirac a) where
  toMeasurePreserving := MeasurePreserving.id _
  aeconst_set s hs hpre :=
    eventuallyConst_iff_exists_eventuallyEq.mpr ⟨s a, ae_eq_dirac s⟩

theorem classify (μ : Measure Ω) [IsProbabilityMeasure μ] (hμ : Ergodic T μ) :
    μ = Measure.dirac 0 ∨ μ = Measure.dirac 1 := by
  have hc : ({(0 : Ω)} : Set Ω)ᶜ = {1} := by
    ext i
    fin_cases i <;> simp
  have hsum : μ {1} = 1 - μ {0} := by
    simpa [hc] using measure_compl (measurableSet_singleton (0 : Ω)) (measure_ne_top μ {0})
  rcases hμ.toPreErgodic.prob_eq_zero_or_one (measurableSet_singleton (0 : Ω)) rfl with h0 | h0
  · right
    have h1 : μ {1} = 1 := by simpa [h0] using hsum
    apply Measure.ext_of_singleton
    intro i
    fin_cases i <;> simp [h0, h1]
  · left
    have h1 : μ {1} = 0 := by simpa [h0] using hsum
    apply Measure.ext_of_singleton
    intro i
    fin_cases i <;> simp [h0, h1]

theorem ergodic_iff (μ : Measure Ω) [IsProbabilityMeasure μ] :
    Ergodic T μ ↔ μ = Measure.dirac 0 ∨ μ = Measure.dirac 1 := by
  constructor
  · exact classify μ
  · rintro (rfl | rfl) <;> exact dirac_ergodic _

def pair (μ : Measure Ω) : ℝ × ℝ := (∫ x, f x ∂μ, ∫ x, g x ∂μ)
def a : ℝ × ℝ := (1, 0)
def b : ℝ × ℝ := (0, 1)

theorem integral_zero : pair (Measure.dirac 0) = a := by simp [pair, f, g, a]
theorem integral_one : pair (Measure.dirac 1) = b := by simp [pair, f, g, b]

def image : Set (ℝ × ℝ) := {p | ∃ μ : Measure Ω,
  IsProbabilityMeasure μ ∧ Ergodic T μ ∧ pair μ = p}

theorem image_exact : image = {a, b} := by
  ext p
  constructor
  · rintro ⟨μ, hprob, hμ, hp⟩
    letI := hprob
    rcases classify μ hμ with h | h
    · rw [h, integral_zero] at hp
      exact Set.mem_insert_iff.mpr (Or.inl hp.symm)
    · rw [h, integral_one] at hp
      exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr hp.symm))
  · intro hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl
    · exact ⟨Measure.dirac 0, inferInstance, dirac_ergodic 0, integral_zero⟩
    · exact ⟨Measure.dirac 1, inferInstance, dirac_ergodic 1, integral_one⟩

/-- Genuine northeast Pareto maximality, quantified over the full integration image. -/
def frontier : Set (ℝ × ℝ) := {p | p ∈ image ∧
  ∀ q ∈ image, p.1 ≤ q.1 → p.2 ≤ q.2 → q = p}

theorem frontier_exact : frontier = {a, b} := by
  ext p
  constructor
  · intro hp
    exact image_exact ▸ hp.1
  · intro hp
    refine ⟨image_exact.symm ▸ hp, ?_⟩
    intro q hq hx hy
    rw [image_exact] at hq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp hq
    rcases hp with rfl | rfl <;> rcases hq with rfl | rfl <;>
      norm_num [a, b] at hx hy ⊢

theorem not_convex : ¬ Convex ℝ frontier := by
  intro h
  have ha : a ∈ frontier := by rw [frontier_exact]; simp
  have hb : b ∈ frontier := by rw [frontier_exact]; simp
  have hm := h ha hb (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  norm_num [frontier_exact, a, b, Prod.smul_mk, smul_eq_mul] at hm

theorem counterexample : Ergodic T (Measure.dirac 0) ∧
    image = {a, b} ∧ frontier = {a, b} ∧ ¬ Convex ℝ frontier :=
  ⟨dirac_ergodic 0, image_exact, frontier_exact, not_convex⟩

end ParetoCounterexample
end

#print axioms ParetoCounterexample.dirac_ergodic
#print axioms ParetoCounterexample.ergodic_iff
#print axioms ParetoCounterexample.integral_zero
#print axioms ParetoCounterexample.image_exact
#print axioms ParetoCounterexample.frontier_exact
#print axioms ParetoCounterexample.counterexample
