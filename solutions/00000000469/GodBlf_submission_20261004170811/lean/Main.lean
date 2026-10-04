import Mathlib.Basic.Real.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Logic.Relation
import Mathlib.Tactic

/-! Standard subset expansions of flow and tension polynomials, evaluated over ℝ.
Components are actual graph components, defined by the equivalence closure of
the selected edges. No component counts or polynomial values are assumed. -/
namespace Conjecture469

structure Graph (n : ℕ) where
  tail : Fin 3 → Fin n
  head : Fin 3 → Fin n

def triangle : Graph 3 where
  tail := ![0, 1, 2]
  head := ![1, 2, 0]

def tripleBond : Graph 2 where
  tail := fun _ => 0
  head := fun _ => 1

def adjacency {n : ℕ} (G : Graph n) (A : Finset (Fin 3)) (u v : Fin n) : Prop :=
  ∃ e ∈ A, G.tail e = u ∧ G.head e = v

noncomputable def components {n : ℕ} (G : Graph n) (A : Finset (Fin 3)) : ℕ :=
  Nat.card (Quotient (Relation.EqvGen.setoid (adjacency G A)))

noncomputable def flow {n : ℕ} (G : Graph n) (q : ℝ) : ℝ :=
  ∑ A ∈ (Finset.univ : Finset (Fin 3)).powerset,
    (-1 : ℝ) ^ (3 - A.card) * q ^ (A.card + components G A - n)

noncomputable def tension {n : ℕ} (G : Graph n) (q : ℝ) : ℝ :=
  ∑ A ∈ (Finset.univ : Finset (Fin 3)).powerset,
    (-1 : ℝ) ^ A.card * q ^ (components G A - components G Finset.univ)

private theorem all_subsets :
    (Finset.univ : Finset (Fin 3)).powerset =
      {∅, {0}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}} := by decide

theorem flow_at_one {n : ℕ} (G : Graph n) : flow G 1 = 0 := by
  rw [flow, all_subsets]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Finset.ext_iff, Fin.forall_fin_succ]

theorem tension_at_one {n : ℕ} (G : Graph n) : tension G 1 = 0 := by
  rw [tension, all_subsets]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Finset.ext_iff, Fin.forall_fin_succ]

theorem triangle_connected (u v : Fin 3) :
    Relation.EqvGen (adjacency triangle Finset.univ) u v := by
  fin_cases u <;> fin_cases v
  all_goals first
  | exact .refl _
  | exact .rel _ _ (by unfold adjacency; decide)
  | exact .symm _ _ (.rel _ _ (by unfold adjacency; decide))

theorem tripleBond_connected (u v : Fin 2) :
    Relation.EqvGen (adjacency tripleBond Finset.univ) u v := by
  fin_cases u <;> fin_cases v
  all_goals first
  | exact .refl _
  | exact .rel _ _ (by unfold adjacency; decide)
  | exact .symm _ _ (.rel _ _ (by unfold adjacency; decide))

/-! A combinatorial plane embedding of the triangle. Dart (e,false) goes
along the orientation; (e,true) goes against it. `reverse` is edge reversal,
`rotation` exchanges the two darts at each vertex. Faces are the cycles of
rotation ∘ reverse: the three forward darts and the three backward darts. -/
abbrev Dart := Fin 3 × Bool

def reverse (d : Dart) : Dart := (d.1, !d.2)
def nextEdge : Fin 3 → Fin 3 := ![1, 2, 0]
def prevEdge : Fin 3 → Fin 3 := ![2, 0, 1]
def rotation (d : Dart) : Dart :=
  if d.2 then (nextEdge d.1, false) else (prevEdge d.1, true)
def faceStep (d : Dart) : Dart := rotation (reverse d)
def vertexOf (d : Dart) : Fin 3 :=
  if d.2 then triangle.head d.1 else triangle.tail d.1
def faceOf (d : Dart) : Fin 2 := if d.2 then 1 else 0

theorem rotation_at_vertex (d : Dart) : vertexOf (rotation d) = vertexOf d := by
  rcases d with ⟨e, b⟩
  fin_cases e <;> cases b <;> decide

theorem rotation_involution (d : Dart) : rotation (rotation d) = d := by
  rcases d with ⟨e, b⟩
  fin_cases e <;> cases b <;> decide

theorem faces_are_cycles (d : Dart) :
    faceOf (faceStep d) = faceOf d ∧
    faceStep (faceStep (faceStep d)) = d ∧ faceStep d ≠ d := by
  rcases d with ⟨e, b⟩
  fin_cases e <;> cases b <;> decide

-- Each label has exactly one three-dart face cycle, not several cycles.
theorem face_cycles_exhaust (d : Dart) :
    d = ((0 : Fin 3), d.2) ∨
    d = faceStep ((0 : Fin 3), d.2) ∨
    d = faceStep (faceStep ((0 : Fin 3), d.2)) := by
  rcases d with ⟨e, b⟩
  fin_cases e <;> cases b <;> decide

theorem euler_sphere : (3 : ℤ) - 3 + 2 = 2 := by norm_num

-- The dual endpoints are the two faces on the two sides of each edge.
theorem dual_incidence (e : Fin 3) :
    tripleBond.tail e = faceOf (e, false) ∧
    tripleBond.head e = faceOf (e, true) := by
  fin_cases e <;> decide

noncomputable def separated : Prop :=
  ∀ q : ℝ, ¬ (flow triangle q = 0 ∧ tension tripleBond q = 0)

theorem common_real_root :
    ∃ q : ℝ, flow triangle q = 0 ∧ tension tripleBond q = 0 :=
  ⟨1, flow_at_one triangle, tension_at_one tripleBond⟩

theorem conjecture_false : ¬ separated := by
  intro h
  exact h 1 ⟨flow_at_one triangle, tension_at_one tripleBond⟩

end Conjecture469
