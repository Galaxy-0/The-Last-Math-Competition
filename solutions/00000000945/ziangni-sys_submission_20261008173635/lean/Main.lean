import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Analysis.InnerProductSpace.PiL2

open scoped NNReal

namespace CircleExtension

abbrev Plane := EuclideanSpace ℝ (Fin 2)
abbrev Circle := {x : Plane // x ∈ Metric.sphere (0 : Plane) 1}

/-- McShane extension, for a genuine function on a metric-space subset. -/
theorem subset_extension {X : Type*} [MetricSpace X] (s : Set X)
    (f : s → ℝ) (K : ℝ≥0) (hf : LipschitzWith K f) :
    ∃ g : X → ℝ, LipschitzWith K g ∧ ∀ x : s, g x = f x := by
  classical
  let F : X → ℝ := fun x => if hx : x ∈ s then f ⟨x, hx⟩ else 0
  have hF : LipschitzOnWith K F s := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    simpa only [F, dif_pos hx, dif_pos hy, Subtype.dist_eq] using
      hf.dist_le_mul (⟨x, hx⟩ : s) (⟨y, hy⟩ : s)
  obtain ⟨g, hg, hEq⟩ := hF.extend_real
  refine ⟨g, hg, ?_⟩
  intro x
  have he := hEq x.property
  simpa only [F, dif_pos x.property] using he.symm

/-- Every real-valued Lipschitz function on the actual Euclidean unit circle extends. -/
theorem circle_extension (f : Circle → ℝ) (K : ℝ≥0) (hf : LipschitzWith K f) :
    ∃ g : Plane → ℝ, LipschitzWith K g ∧ ∀ x : Circle, g x = f x :=
  subset_extension (Metric.sphere (0 : Plane) 1) f K hf

/-- The existential obstruction asserted in the conjecture is false. -/
theorem conjecture_false :
    ¬ ∃ f : Circle → ℝ, (∃ K : ℝ≥0, LipschitzWith K f) ∧
      ¬ ∃ g : Plane → ℝ, (∃ L : ℝ≥0, LipschitzWith L g) ∧
        ∀ x : Circle, g x = f x := by
  rintro ⟨f, ⟨K, hf⟩, hno⟩
  obtain ⟨g, hg, he⟩ := circle_extension f K hf
  exact hno ⟨g, ⟨K, hg⟩, he⟩

/-- The same extension can be regarded as taking values in a Banach plane. -/
theorem plane_target_extension (f : Circle → ℝ) (K : ℝ≥0) (hf : LipschitzWith K f) :
    ∃ g : Plane → ℝ × ℝ, LipschitzWith K g ∧
      ∀ x : Circle, g x = (f x, 0) := by
  obtain ⟨g, hg, he⟩ := circle_extension f K hf
  refine ⟨fun x => (g x, 0), ?_, ?_⟩
  · simpa using hg.prodMk (LipschitzWith.const (0 : ℝ))
  · intro x
    simp only [he x]

end CircleExtension

#print axioms CircleExtension.subset_extension
#print axioms CircleExtension.circle_extension
#print axioms CircleExtension.conjecture_false
#print axioms CircleExtension.plane_target_extension
