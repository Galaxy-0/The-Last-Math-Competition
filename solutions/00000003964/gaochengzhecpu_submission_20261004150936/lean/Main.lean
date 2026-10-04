import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Linarith

namespace Conjecture3964

noncomputable section
open SimpleGraph

abbrev G := ZMod 1021

instance : Fact (Nat.Prime 1021) := ⟨by norm_num⟩

theorem group_simple : IsSimpleAddGroup G := inferInstance

theorem group_card : Fintype.card G = 1021 := by simp

def graph : SimpleGraph G := cycleGraph 1021

theorem graph_is_cayley : graph = circulantGraph ({1} : Set G) := rfl

theorem generator_generates : AddSubgroup.closure ({1} : Set G) = ⊤ := by
  apply top_unique
  intro x _
  have h1 : (1 : G) ∈ AddSubgroup.closure ({1} : Set G) :=
    AddSubgroup.subset_closure (by simp)
  have h := (AddSubgroup.closure ({1} : Set G)).nsmul_mem h1 x.val
  simpa using h

theorem graph_connected : graph.Connected := cycleGraph_connected

/-- A distance lower-bound potential on the actual cycle vertices. -/
def potential (v : G) : ℕ := min (v : Fin 1021).val (1021 - (v : Fin 1021).val)

theorem cyclic_potential_step (a b : ℕ) (ha : a < 1021) (hb : b < 1021)
    (h : (1021 - b + a) % 1021 = 1 ∨ (1021 - a + b) % 1021 = 1) :
    min b (1021 - b) ≤ min a (1021 - a) + 1 := by
  simp only [Nat.min_def]
  split_ifs <;> omega

theorem edge_potential {u v : G} (h : graph.Adj u v) :
    potential v ≤ potential u + 1 := by
  have ha : ((u : Fin 1021) - v).val = 1 ∨ ((v : Fin 1021) - u).val = 1 :=
    cycleGraph_adj'.mp h
  change (1021 - (v : Fin 1021).val + (u : Fin 1021).val) % 1021 = 1 ∨
    (1021 - (u : Fin 1021).val + (v : Fin 1021).val) % 1021 = 1 at ha
  exact cyclic_potential_step (Fin.val u) (Fin.val v) u.isLt v.isLt ha

theorem potential_le_walk {u v : G} (w : graph.Walk u v) :
    potential v ≤ potential u + w.length := by
  induction w with
  | nil => simp
  | @cons a b c h w ih =>
    have he := edge_potential h
    simp only [Walk.length_cons]
    omega

theorem distance_lower : 510 ≤ graph.dist 0 510 := by
  obtain ⟨w, hw⟩ := graph_connected.exists_walk_length_eq_dist 0 510
  have h := potential_le_walk w
  have h0 : potential 0 = 0 := by decide
  have h510 : potential 510 = 510 := by decide
  rw [h0, h510, hw, zero_add] at h
  exact h

/-- Diameter as the actual maximum of graph distances in a finite graph. -/
def diameter {V : Type*} [Fintype V] (H : SimpleGraph V) : ℕ :=
  Finset.univ.sup (fun u => Finset.univ.sup (fun v => H.dist u v))

theorem distance_le_diameter {V : Type*} [Fintype V]
    (H : SimpleGraph V) (u v : V) : H.dist u v ≤ diameter H := by
  exact (Finset.le_sup (f := fun v => H.dist u v) (Finset.mem_univ v)).trans
    (Finset.le_sup (f := fun u => Finset.univ.sup (fun v => H.dist u v))
      (Finset.mem_univ u))

theorem diameter_lower : 510 ≤ diameter graph :=
  distance_lower.trans (distance_le_diameter graph 0 510)

theorem log_card_lt_ten : Real.log (Fintype.card G) < 10 := by
  rw [group_card]
  change Real.log (1021 : ℝ) < 10
  have hlog2 : Real.log 2 < 1 := by
    have h := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (2 : ℝ) ≠ 1)
    norm_num at h ⊢
    exact h
  have hmono : Real.log (1021 : ℝ) < Real.log ((2 : ℝ) ^ 10) :=
    Real.log_lt_log (by norm_num) (by norm_num)
  rw [Real.log_pow] at hmono
  norm_num at hmono
  linarith

theorem proposed_bound_lt_diameter :
    3 * (Real.log (Fintype.card G)) ^ 2 < (diameter graph : ℝ) := by
  have hn : 0 ≤ Real.log (Fintype.card G) := by
    apply Real.log_nonneg
    rw [group_card]
    norm_num
  have hl := log_card_lt_ten
  have hd : (510 : ℝ) ≤ (diameter graph : ℝ) := by exact_mod_cast diameter_lower
  nlinarith

/-- The same example also defeats the bound when log means base two. -/
theorem binary_bound_lt_diameter :
    3 * (Real.log (Fintype.card G) / Real.log 2) ^ 2 < (diameter graph : ℝ) := by
  have hp : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hmono : Real.log (1021 : ℝ) < Real.log ((2 : ℝ) ^ 10) :=
    Real.log_lt_log (by norm_num) (by norm_num)
  rw [Real.log_pow] at hmono
  have hl : Real.log (1021 : ℝ) / Real.log 2 < 10 := by
    apply (div_lt_iff₀ hp).2
    norm_num at hmono
    linarith
  have hn : 0 ≤ Real.log (1021 : ℝ) / Real.log 2 :=
    div_nonneg (Real.log_nonneg (by norm_num)) hp.le
  have hd : (510 : ℝ) ≤ (diameter graph : ℝ) := by exact_mod_cast diameter_lower
  rw [group_card]
  norm_num only [Nat.cast_ofNat]
  nlinarith

/-- A necessary universal clause, written in additive group notation. -/
def ClaimedDiameterBound : Prop :=
  ∀ (H : Type) [AddGroup H] [Fintype H] [IsSimpleAddGroup H],
    ∀ S : Set H, AddSubgroup.closure S = ⊤ →
      (circulantGraph S).Connected →
      (diameter (circulantGraph S) : ℝ) ≤ 3 * (Real.log (Fintype.card H)) ^ 2

theorem conjecture_false : ¬ ClaimedDiameterBound := by
  intro h
  have hb := h G {1} generator_generates graph_connected
  exact (not_le_of_gt proposed_bound_lt_diameter) hb

#print axioms group_simple
#print axioms generator_generates
#print axioms graph_connected
#print axioms potential_le_walk
#print axioms distance_lower
#print axioms diameter_lower
#print axioms log_card_lt_ten
#print axioms proposed_bound_lt_diameter
#print axioms binary_bound_lt_diameter
#print axioms conjecture_false

end
end Conjecture3964
