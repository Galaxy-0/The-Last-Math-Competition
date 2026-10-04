import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

namespace PositiveCompletionCounterexample

abbrev H := EuclideanSpace ℝ (Fin 3)
abbrev Operator := H →L[ℝ] H
noncomputable def e (i : Fin 3) : H := EuclideanSpace.basisFun (Fin 3) ℝ i

/-- Entries in the actual standard orthonormal basis of the real Hilbert space. -/
noncomputable def entry (T : Operator) (i j : Fin 3) : ℝ := @inner ℝ H _ (e i) (T (e j))

def Positive (T : Operator) : Prop :=
  (∀ x y : H, @inner ℝ H _ x (T y) = @inner ℝ H _ (T x) y) ∧
  (∀ x : H, 0 ≤ @inner ℝ H _ x (T x))

/-- All entries are specified zero except the single central entry (1,1). -/
def Completes (T : Operator) : Prop := Positive T ∧
  ∀ i j : Fin 3, i ≠ 1 ∨ j ≠ 1 → entry T i j = 0

def Loewner (S T : Operator) : Prop :=
  ∀ x : H, @inner ℝ H _ x (S x) ≤ @inner ℝ H _ x (T x)

def NormMinimal (T : Operator) : Prop := Completes T ∧
  ∀ S : Operator, Completes S → ‖T‖ ≤ ‖S‖

def LoewnerMinimal (T : Operator) : Prop := Completes T ∧
  ∀ S : Operator, Completes S → Loewner S T → Loewner T S

theorem zero_completes : Completes 0 := by
  constructor
  · constructor <;> intros <;> simp
  · intro i j hij
    simp [entry]

theorem zero_least (T : Operator) (hT : Completes T) : Loewner 0 T := by
  intro x
  simpa using hT.1.2 x

/-- Polarization establishes antisymmetry on the actual positive operators. -/
theorem positive_le_zero (T : Operator) (hT : Positive T) (h : Loewner T 0) : T = 0 := by
  have hq : ∀ x : H, @inner ℝ H _ x (T x) = 0 := by
    intro x
    have hu := h x
    simp only [ContinuousLinearMap.zero_apply, inner_zero_right] at hu
    exact le_antisymm hu (hT.2 x)
  apply ContinuousLinearMap.ext
  intro x
  have hxy := hq (x + T x)
  simp only [map_add, inner_add_left, inner_add_right] at hxy
  have hc := hT.1 x (T x)
  rw [hq x, hq (T x), hc] at hxy
  have hn : @inner ℝ H _ (T x) (T x) = 0 := by linarith
  exact inner_self_eq_zero.mp hn

theorem norm_minimal_iff (T : Operator) : NormMinimal T ↔ T = 0 := by
  constructor
  · intro hT
    have h := hT.2 0 zero_completes
    simp only [norm_zero] at h
    exact norm_eq_zero.mp (le_antisymm h (norm_nonneg T))
  · rintro rfl
    exact ⟨zero_completes, fun S _ => by simp⟩

theorem loewner_minimal_iff (T : Operator) : LoewnerMinimal T ↔ T = 0 := by
  constructor
  · intro hT
    exact positive_le_zero T hT.1.1 (hT.2 0 zero_completes (zero_least T hT.1))
  · rintro rfl
    exact ⟨zero_completes, fun S hS _ => zero_least S hS⟩

def IsCorner (i j : Fin 3) : Prop := (i = 0 ∨ i = 2) ∧ (j = 0 ∨ j = 2)

theorem central_not_corner : ¬ IsCorner 1 1 := by unfold IsCorner; decide

theorem counterexample :
    (∃! T : Operator, NormMinimal T) ∧
    (∃! T : Operator, LoewnerMinimal T) ∧ ¬ IsCorner 1 1 := by
  refine ⟨⟨0, (norm_minimal_iff 0).mpr rfl, ?_⟩,
    ⟨0, (loewner_minimal_iff 0).mpr rfl, ?_⟩, central_not_corner⟩
  · intro T hT
    exact (norm_minimal_iff T).mp hT
  · intro T hT
    exact (loewner_minimal_iff T).mp hT

end PositiveCompletionCounterexample

#print axioms PositiveCompletionCounterexample.zero_completes
#print axioms PositiveCompletionCounterexample.zero_least
#print axioms PositiveCompletionCounterexample.positive_le_zero
#print axioms PositiveCompletionCounterexample.norm_minimal_iff
#print axioms PositiveCompletionCounterexample.loewner_minimal_iff
#print axioms PositiveCompletionCounterexample.counterexample
