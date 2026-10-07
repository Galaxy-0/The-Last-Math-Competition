import Mathlib.Topology.GDelta.Basic
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith

open Set
namespace Conjecture320

/-- A Hall ray, allowing its initial endpoint to be omitted. -/
def HasHallRay (S : Set ℝ) : Prop := ∃ a : ℝ, Ioi a ⊆ S

theorem nowhere_dense_no_ray (S : Set ℝ) (hS : IsNowhereDense S) : ¬ HasHallRay S := by
  rintro ⟨a, ha⟩
  have hi : Ioi a ⊆ interior (closure S) :=
    interior_maximal (ha.trans subset_closure) isOpen_Ioi
  have hm := hi (show a + 1 ∈ Ioi a by simp)
  rw [hS] at hm
  exact hm

theorem totally_disconnected_no_ray (S : Set ℝ) (hS : IsTotallyDisconnected S) :
    ¬ HasHallRay S := by
  rintro ⟨a, ha⟩
  have hsub : Icc (a + 1) (a + 2) ⊆ S := by
    intro x hx
    apply ha
    change a < x
    linarith [hx.1]
  have hs := hS (Icc (a + 1) (a + 2)) hsub isPreconnected_Icc
  have he : a + 1 = a + 2 := hs (by constructor <;> linarith) (by constructor <;> linarith)
  linarith

/-- No real set can have the two stated properties, even without the threshold 4. -/
theorem incompatible_topological_clauses :
    ¬ ∃ S : Set ℝ, IsTotallyDisconnected S ∧ HasHallRay S := by
  rintro ⟨S, hs, hr⟩
  exact totally_disconnected_no_ray S hs hr

theorem conjectured_before_four_clause_false (S : Set ℝ) (hS : IsTotallyDisconnected S) :
    ¬ ∃ a : ℝ, a < 4 ∧ Ioi a ⊆ S := by
  rintro ⟨a, _, ha⟩
  exact totally_disconnected_no_ray S hS ⟨a, ha⟩

theorem closed_ray_also_impossible (S : Set ℝ) (hS : IsTotallyDisconnected S) (a : ℝ) :
    ¬ Ici a ⊆ S := by
  intro ha
  exact totally_disconnected_no_ray S hS ⟨a, Ioi_subset_Ici_self.trans ha⟩

#print axioms nowhere_dense_no_ray
#print axioms totally_disconnected_no_ray
#print axioms incompatible_topological_clauses
#print axioms conjectured_before_four_clause_false
#print axioms closed_ray_also_impossible
end Conjecture320
