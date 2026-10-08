import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkCounting
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Data.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

namespace Conjecture3711
open SimpleGraph Matrix
open scoped BigOperators
abbrev V := Fin 3
abbrev Mask := Fin 3 → Bool

lemma sum_three (f : V → ℝ) : (∑ i, f i) =
    f ⟨0,by decide⟩ + f ⟨1,by decide⟩ + f ⟨2,by decide⟩ := Fin.sum_univ_three f

def graphOf (m : Mask) : SimpleGraph V :=
  SimpleGraph.fromRel (fun u v =>
    (u = 0 ∧ v = 1 ∧ m 0 = true) ∨
    (u = 0 ∧ v = 2 ∧ m 1 = true) ∨
    (u = 1 ∧ v = 2 ∧ m 2 = true))

instance (m : Mask) : DecidableRel (graphOf m).Adj := by
  intro u v
  dsimp only [graphOf, SimpleGraph.fromRel]
  infer_instance

def edgeCount (m : Mask) : ℕ := (Finset.univ.filter (fun i => m i = true)).card

theorem tree_iff (m : Mask) : (graphOf m).IsTree ↔ edgeCount m = 2 := by
  rw [SimpleGraph.isTree_iff_connected_and_card]
  rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card, Nat.card_eq_fintype_card]
  exact (show ∀ m : Mask, (graphOf m).Connected ∧
    (graphOf m).edgeFinset.card + 1 = Fintype.card V ↔ edgeCount m = 2 by decide) m

noncomputable def maskOf (G : SimpleGraph V) : Mask := by
  classical
  exact ![decide (G.Adj 0 1), decide (G.Adj 0 2), decide (G.Adj 1 2)]

theorem graphOf_maskOf (G : SimpleGraph V) : graphOf (maskOf G) = G := by
  classical
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [graphOf, SimpleGraph.fromRel, maskOf, SimpleGraph.adj_comm] <;>
      exact G.adj_comm _ _

theorem maskOf_graphOf (m : Mask) : maskOf (graphOf m) = m := by
  classical
  funext i
  fin_cases i <;> simp [graphOf, SimpleGraph.fromRel, maskOf]

def K3 : SimpleGraph V := ⊤
instance : DecidableRel K3.Adj := inferInstanceAs (DecidableRel (⊤ : SimpleGraph V).Adj)

abbrev SpanningTree := {T : SimpleGraph V // T ≤ K3 ∧ T.IsTree}

noncomputable def treeEquiv : {m : Mask // edgeCount m = 2} ≃ SpanningTree where
  toFun m := ⟨graphOf m.1, le_top, (tree_iff m.1).2 m.2⟩
  invFun T := ⟨maskOf T.1, (tree_iff _).1 (by rw [graphOf_maskOf]; exact T.2.2)⟩
  left_inv m := Subtype.ext (maskOf_graphOf m.1)
  right_inv T := Subtype.ext (graphOf_maskOf T.1)

theorem spanning_tree_count : Nat.card SpanningTree = 3 := by
  rw [← Nat.card_congr treeEquiv, Nat.card_eq_fintype_card]
  decide

noncomputable def L : Matrix V V ℝ := !![2,-1,-1; -1,2,-1; -1,-1,2]
noncomputable def Q : Matrix V V ℝ :=
  !![2/9,-1/9,-1/9; -1/9,2/9,-1/9; -1/9,-1/9,2/9]

theorem actual_laplacian : K3.lapMatrix ℝ = L := by
  have hd : ∀ i : V, K3.degree i = 2 := by decide
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
      SimpleGraph.adjMatrix, hd, K3, L, Fin.ext_iff]

/-- The four defining Moore-Penrose equations over the real numbers. -/
def IsMoorePenrose (A B : Matrix V V ℝ) : Prop :=
  A * B * A = A ∧ B * A * B = B ∧ (A * B).transpose = A * B ∧
    (B * A).transpose = B * A

theorem actual_pseudoinverse : IsMoorePenrose (K3.lapMatrix ℝ) Q := by
  rw [actual_laplacian]
  unfold IsMoorePenrose
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [L, Q, Matrix.mul_apply, Fin.sum_univ_succ, Fin.ext_iff]

noncomputable def current (s t : V) : V → ℝ := fun i =>
  (if i = s then 1 else 0) - (if i = t then 1 else 0)
noncomputable def voltage (s t : V) : V → ℝ := Q *ᵥ current s t
noncomputable def resistance (s t : V) : ℝ :=
  (current s t) ⬝ᵥ (Q *ᵥ current s t)

theorem solves_unit_current (s t : V) : K3.lapMatrix ℝ *ᵥ voltage s t = current s t := by
  rw [actual_laplacian]
  funext i
  fin_cases s <;> fin_cases t <;> fin_cases i <;>
    norm_num [L, Q, current, voltage, mulVec, dotProduct, sum_three]

theorem voltage_drop (s t : V) : resistance s t = voltage s t s - voltage s t t := by
  fin_cases s <;> fin_cases t <;>
    norm_num [resistance, voltage, current, Q, mulVec, dotProduct, sum_three]

theorem resistance_value (s t : V) : resistance s t = if s = t then 0 else 2/3 := by
  fin_cases s <;> fin_cases t <;>
    norm_num [resistance, current, Q, mulVec, dotProduct, sum_three]

theorem kernel_constant (v : V → ℝ) (hv : L *ᵥ v = 0) : ∀ i, v i = v 0 := by
  have h0 := congrFun hv 0
  have h1 := congrFun hv 1
  norm_num [L, mulVec, dotProduct, sum_three] at h0 h1
  intro i
  fin_cases i
  · rfl
  · change v 1 = v 0
    linarith
  · change v ⟨2, by decide⟩ = v 0
    linarith

/-- Every voltage solving Kirchhoff's equation has the same terminal drop. -/
theorem electrical_resistance (s t : V) (v : V → ℝ)
    (hv : K3.lapMatrix ℝ *ᵥ v = current s t) :
    v s - v t = resistance s t := by
  have hk : L *ᵥ (v - voltage s t) = 0 := by
    rw [← actual_laplacian, Matrix.mulVec_sub, hv, solves_unit_current, sub_self]
  have hs := kernel_constant (v - voltage s t) hk s
  have ht := kernel_constant (v - voltage s t) hk t
  simp only [Pi.sub_apply] at hs ht
  rw [voltage_drop]
  linarith

theorem unordered_sum : (∑ s : V, ∑ t : V, if s < t then resistance s t else 0) = 2 := by
  have h02 : (0 : V) < ⟨2, by decide⟩ := by decide
  have h12 : (1 : V) < ⟨2, by decide⟩ := by decide
  norm_num [resistance_value, sum_three, h02, h12]

theorem ordered_sum : (∑ s : V, ∑ t : V, resistance s t) = 4 := by
  norm_num [resistance_value, sum_three]

theorem unordered_conjecture_false :
    (∑ s : V, ∑ t : V, if s < t then resistance s t else 0) ≠ (Nat.card SpanningTree : ℝ) := by
  rw [unordered_sum, spanning_tree_count]
  norm_num

theorem ordered_conjecture_false :
    (∑ s : V, ∑ t : V, resistance s t) ≠ (Nat.card SpanningTree : ℝ) := by
  rw [ordered_sum, spanning_tree_count]
  norm_num

#print axioms tree_iff
#print axioms graphOf_maskOf
#print axioms spanning_tree_count
#print axioms actual_laplacian
#print axioms actual_pseudoinverse
#print axioms solves_unit_current
#print axioms voltage_drop
#print axioms resistance_value
#print axioms electrical_resistance
#print axioms unordered_conjecture_false
#print axioms ordered_conjecture_false
end Conjecture3711
