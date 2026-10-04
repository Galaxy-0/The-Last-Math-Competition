import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Tactic.NormNum

/-! A bounded subset of a genuine infinite-dimensional Hilbert space cannot
be covered by finitely many subsets of strictly smaller diameter. -/

namespace Conjecture3556

open scoped BigOperators ENNReal

/-- The actual Hilbert space of square-summable real sequences. -/
abbrev E := lp (fun _ : ℕ => ℝ) 2

theorem space_complete : CompleteSpace E := inferInstance

/-- The n-th coordinate unit vector in l-two. -/
noncomputable def e (n : ℕ) : E := lp.single 2 n 1

@[simp] theorem e_apply (n k : ℕ) : e n k = if k = n then 1 else 0 := by
  simp [e, Pi.single_apply]

theorem norm_e (n : ℕ) : ‖e n‖ = 1 := by
  rw [e, lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)]
  norm_num

theorem unit_vectors_independent : LinearIndependent ℝ e := by
  classical
  rw [linearIndependent_iff']
  intro s g h i hi
  have heval := congrArg (fun x : E => x i) h
  simpa [lp.coeFn_sum, lp.coeFn_smul, e_apply, hi] using heval

/-- Infinite linear independence rules out finite dimension in the actual ambient space. -/
theorem space_infinite_dimensional : ¬ FiniteDimensional ℝ E := by
  intro h
  letI := h
  have hc := unit_vectors_independent.lt_aleph0_of_finiteDimensional
  simp at hc

theorem inner_unit_vectors {i j : ℕ} (hij : i ≠ j) : @inner ℝ E _ (e i) (e j) = 0 := by
  simp [e, lp.inner_single_left, Pi.single_apply, hij]

theorem distance_unit_vectors {i j : ℕ} (hij : i ≠ j) :
    dist (e i) (e j) = Real.sqrt 2 := by
  have hs : ‖e i - e j‖ ^ 2 = 2 := by
    rw [norm_sub_sq_real, norm_e, norm_e, inner_unit_vectors hij]
    norm_num
  rw [dist_eq_norm]
  exact ((Real.sqrt_eq_iff_eq_sq (by norm_num) (norm_nonneg _)).2 hs.symm).symm

def S : Set E := Set.range e

theorem S_nonempty : S.Nonempty := ⟨e 0, ⟨0, rfl⟩⟩

theorem S_distance_le : ∀ x ∈ S, ∀ y ∈ S, dist x y ≤ Real.sqrt 2 := by
  rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
  by_cases hij : i = j
  · simp [hij]
  · exact (distance_unit_vectors hij).le

theorem S_bounded : Bornology.IsBounded S :=
  Metric.isBounded_iff.mpr ⟨Real.sqrt 2, S_distance_le⟩

theorem S_diameter : Metric.diam S = Real.sqrt 2 := by
  apply le_antisymm
  · exact Metric.diam_le_of_forall_dist_le (by norm_num) S_distance_le
  · have h := Metric.dist_le_diam_of_mem S_bounded
        (show e 0 ∈ S from ⟨0, rfl⟩) (show e 1 ∈ S from ⟨1, rfl⟩)
    simpa [distance_unit_vectors (by decide : (0 : ℕ) ≠ 1)] using h

/-- A diameter-reducing finite cover uses actual subsets of S. This ensures
boundedness of every part, so Metric.diam is the genuine finite diameter. -/
def FiniteSmallerDiameterCover (s : Set E) : Prop :=
  ∃ (n : ℕ) (parts : Fin n → Set E),
    (∀ c, parts c ⊆ s) ∧
    (∀ x ∈ s, ∃ c, x ∈ parts c) ∧
    (∀ c, Metric.diam (parts c) < Metric.diam s)

/-- No finite coloring can give a smaller-diameter color class at every color. -/
theorem no_finite_smaller_diameter_cover : ¬ FiniteSmallerDiameterCover S := by
  classical
  rintro ⟨n, parts, hsub, hcover, hsmall⟩
  have hex : ∀ i : ℕ, ∃ c : Fin n, e i ∈ parts c :=
    fun i => hcover (e i) ⟨i, rfl⟩
  choose color hcolor using hex
  obtain ⟨i, j, hij, heq⟩ := Finite.exists_ne_map_eq_of_infinite color
  have hi : e i ∈ parts (color i) := hcolor i
  have hj : e j ∈ parts (color i) := by rw [heq]; exact hcolor j
  have hdist := Metric.dist_le_diam_of_mem (S_bounded.subset (hsub (color i))) hi hj
  rw [distance_unit_vectors hij] at hdist
  have hs := hsmall (color i)
  rw [S_diameter] at hs
  exact (not_lt_of_ge hdist) hs

/-- The finiteness clause would imply that every nonempty bounded positive-diameter
subset of this infinite-dimensional space has a finite smaller-diameter cover. -/
def FinitenessClauseInE : Prop :=
  ∀ s : Set E, s.Nonempty → Bornology.IsBounded s → 0 < Metric.diam s →
    FiniteSmallerDiameterCover s

theorem counterexample :
    (¬ FiniteDimensional ℝ E) ∧ S.Nonempty ∧ Bornology.IsBounded S ∧
      Metric.diam S = Real.sqrt 2 ∧ ¬ FiniteSmallerDiameterCover S :=
  ⟨space_infinite_dimensional, S_nonempty, S_bounded, S_diameter,
    no_finite_smaller_diameter_cover⟩

theorem conjecture_false : ¬ FinitenessClauseInE := by
  intro h
  exact no_finite_smaller_diameter_cover
    (h S S_nonempty S_bounded (by rw [S_diameter]; exact Real.sqrt_pos.2 (by norm_num)))

#print axioms space_complete
#print axioms unit_vectors_independent
#print axioms space_infinite_dimensional
#print axioms distance_unit_vectors
#print axioms S_bounded
#print axioms S_diameter
#print axioms no_finite_smaller_diameter_cover
#print axioms counterexample
#print axioms conjecture_false

end Conjecture3556
