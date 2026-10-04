import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Combinatorics.SimpleGraph.Acyclic

namespace Transport

abbrev Mat := Bool → Bool → ℝ

/-- The real 2 by 2 transportation polytope with all four margins equal to one. -/
def P : Set Mat := {X | (∀ i j, 0 ≤ X i j) ∧
  (∀ i, X i false + X i true = 1) ∧
  (∀ j, X false j + X true j = 1)}

def diagonal : Mat := fun i j => if i = j then 1 else 0

theorem diagonal_feasible : diagonal ∈ P := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j; cases i <;> cases j <;> simp [diagonal]
  · intro i; cases i <;> simp [diagonal]
  · intro j; cases j <;> simp [diagonal]

/-- A positive weighted sum of nonnegative real numbers can vanish only at zero. -/
theorem weighted_zero {s t x y : ℝ} (hs : 0 < s) (ht : 0 < t)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (h : s*x + t*y = 0) : x = 0 ∧ y = 0 := by
  have hp : s*x = 0 := le_antisymm (by nlinarith [mul_nonneg ht.le hy])
    (mul_nonneg hs.le hx)
  have hq : t*y = 0 := le_antisymm (by nlinarith [mul_nonneg hs.le hx])
    (mul_nonneg ht.le hy)
  exact ⟨(mul_eq_zero.mp hp).resolve_left hs.ne', (mul_eq_zero.mp hq).resolve_left ht.ne'⟩

theorem feasible_of_offdiag_zero {X : Mat} (hX : X ∈ P)
    (h01 : X false true = 0) (h10 : X true false = 0) : X = diagonal := by
  have h00 : X false false = 1 := by simpa [h01] using hX.2.1 false
  have h11 : X true true = 1 := by simpa [h10] using hX.2.1 true
  funext i j
  cases i <;> cases j <;> simp [diagonal, h00, h01, h10, h11]

/-- Membership in Mathlib's actual real extreme-point set, not an integer surrogate. -/
theorem diagonal_extreme : diagonal ∈ P.extremePoints ℝ := by
  refine ⟨diagonal_feasible, ?_⟩
  intro A hA B hB hm
  obtain ⟨s, t, hs, ht, _hst, heq⟩ := hm
  have h01 : s * A false true + t * B false true = 0 := by
    simpa [diagonal] using congrFun (congrFun heq false) true
  have h10 : s * A true false + t * B true false = 0 := by
    simpa [diagonal] using congrFun (congrFun heq true) false
  have hz01 := weighted_zero hs ht (hA.1 false true) (hB.1 false true) h01
  have hz10 := weighted_zero hs ht (hA.1 true false) (hB.1 true false) h10
  exact ⟨feasible_of_offdiag_zero hA hz01.1 hz10.1,
    feasible_of_offdiag_zero hB hz01.2 hz10.2⟩

/-- All row and column vertices are retained. Left denotes a row, right a column. -/
abbrev Node := Sum Bool Bool

/-- The usual bipartite positive-support graph of a transportation matrix. -/
def support (X : Mat) : SimpleGraph Node where
  Adj u v := match u, v with
    | .inl i, .inr j => 0 < X i j
    | .inr j, .inl i => 0 < X i j
    | _, _ => False
  symm := by intro u v; cases u <;> cases v <;> simp
  loopless := by intro u; cases u <;> simp

def index : Node → Bool
  | .inl i => i
  | .inr j => j

theorem support_edge_preserves_index {u v : Node}
    (h : (support diagonal).Adj u v) : index u = index v := by
  cases u with
  | inl i => cases v with
    | inl j => exact False.elim h
    | inr j => cases i <;> cases j <;> simp_all [support, diagonal, index]
  | inr i => cases v with
    | inl j => cases i <;> cases j <;> simp_all [support, diagonal, index]
    | inr j => exact False.elim h

theorem support_walk_preserves_index {u v : Node}
    (p : (support diagonal).Walk u v) : index u = index v := by
  induction p with
  | nil => rfl
  | cons h p ih => exact (support_edge_preserves_index h).trans ih

theorem support_disconnected : ¬ (support diagonal).Connected := by
  intro hc
  obtain ⟨p⟩ := hc (Sum.inl false) (Sum.inl true)
  have h := support_walk_preserves_index p
  exact Bool.false_ne_true h

theorem support_not_tree : ¬ (support diagonal).IsTree :=
  fun h => support_disconnected h.isConnected

/-- The first assertion of conjecture 00000006672 already fails for positive unit margins. -/
theorem counterexample : ∃ X : Mat, X ∈ P.extremePoints ℝ ∧ ¬ (support X).IsTree :=
  ⟨diagonal, diagonal_extreme, support_not_tree⟩

theorem not_all_vertices_have_tree_support :
    ¬ (∀ X ∈ P.extremePoints ℝ, (support X).IsTree) := by
  intro h
  exact support_not_tree (h diagonal diagonal_extreme)

#print axioms Transport.counterexample
#print axioms Transport.not_all_vertices_have_tree_support
end Transport
