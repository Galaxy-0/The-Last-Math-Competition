import CycleFacts
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic

namespace Conjecture464
open SimpleGraph

/-- Spanning trees retain the full vertex type and are tree subgraphs. -/
def SpanningTree (G : SimpleGraph V) := {T : SimpleGraph V // T ≤ G ∧ T.IsTree}

noncomputable def spanningTreeCount (G : SimpleGraph V) : ℕ := Nat.card (SpanningTree G)

theorem cycle_card_edges (n : ℕ) :
    (cycleGraph (n + 3)).edgeFinset.card = n + 3 := by
  have h := (cycleGraph (n + 3)).sum_degrees_eq_twice_card_edges
  simp only [cycleGraph_degree_three_le, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul] at h
  omega

theorem deletion_tree {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hc : Nat.card G.edgeSet = Nat.card V)
    (e : G.edgeSet) (hconn : (G.deleteEdges {e.val}).Connected) :
    (G.deleteEdges {e.val}).IsTree := by
  classical
  have hcf : G.edgeFinset.card = Fintype.card V := by simpa using hc
  apply isTree_iff_connected_and_card.mpr
  refine ⟨hconn, ?_⟩
  have he : e.val ∈ G.edgeFinset := mem_edgeFinset.mpr e.property
  have hpos : 0 < G.edgeFinset.card := Finset.card_pos.mpr ⟨e.val, he⟩
  rw [Nat.card_eq_fintype_card, ← edgeFinset_card, Nat.card_eq_fintype_card]
  have hed : (G.deleteEdges {e.val}).edgeFinset = G.edgeFinset \ {e.val} := by
    apply Finset.coe_injective
    simp only [coe_edgeFinset, Finset.coe_sdiff, Finset.coe_singleton, edgeSet_deleteEdges]
  rw [hed, Finset.card_sdiff (Finset.singleton_subset_iff.mpr he), Finset.card_singleton]
  omega

theorem tree_missing_single_edge {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hc : Nat.card G.edgeSet = Nat.card V) (T : SpanningTree G) :
    ∃ e : G.edgeSet, G.deleteEdges {e.val} = T.val := by
  classical
  have hcf : G.edgeFinset.card = Fintype.card V := by simpa using hc
  have ht := T.property.2.card_edgeFinset
  have hsub := edgeFinset_mono T.property.1
  have hd : (G.edgeFinset \ T.val.edgeFinset).card = 1 := by
    rw [Finset.card_sdiff hsub]
    omega
  obtain ⟨e, he⟩ := Finset.card_eq_one.mp hd
  have heG : e ∈ G.edgeSet := by
    have : e ∈ G.edgeFinset \ T.val.edgeFinset := by rw [he]; simp
    simpa using (Finset.mem_sdiff.mp this).1
  refine ⟨⟨e, heG⟩, ?_⟩
  have hs : G.edgeSet \ T.val.edgeSet = {e} := by
    have hh := congrArg (fun s : Finset (Sym2 V) => (s : Set (Sym2 V))) he
    simpa using hh
  rw [← hs]
  exact G.deleteEdges_sdiff_eq_of_le T.property.1

theorem spanningTreeCount_eq_card_edges {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hc : Nat.card G.edgeSet = Nat.card V)
    (hconn : ∀ e : G.edgeSet, (G.deleteEdges {e.val}).Connected) :
    spanningTreeCount G = Fintype.card V := by
  classical
  let f : G.edgeSet → SpanningTree G := fun e =>
    ⟨G.deleteEdges {e.val}, G.deleteEdges_le _, deletion_tree G hc e (hconn e)⟩
  have hf_inj : Function.Injective f := by
    intro e₁ e₂ heq
    apply Subtype.ext
    have hg := congrArg (fun T : SpanningTree G => T.val.edgeSet) heq
    change (G.deleteEdges {e₁.val}).edgeSet = (G.deleteEdges {e₂.val}).edgeSet at hg
    rw [edgeSet_deleteEdges, edgeSet_deleteEdges] at hg
    by_contra hne
    have hm : e₁.val ∈ G.edgeSet \ {e₂.val} := ⟨e₁.property, by simpa using hne⟩
    rw [← hg] at hm
    exact hm.2 (Set.mem_singleton _)
  have hf_surj : Function.Surjective f := by
    intro T
    obtain ⟨e, he⟩ := tree_missing_single_edge G hc T
    exact ⟨e, Subtype.ext he⟩
  unfold spanningTreeCount
  rw [← Nat.card_congr (Equiv.ofBijective f ⟨hf_inj, hf_surj⟩)]
  simpa using hc

/-- A cycle has exactly one spanning tree for each possible deleted edge. -/
theorem cycle_spanningTreeCount (n : ℕ) :
    spanningTreeCount (cycleGraph (n + 3)) = n + 3 := by
  have hc : Nat.card (cycleGraph (n + 3)).edgeSet = Nat.card (Fin (n + 3)) := by
    simpa only [Nat.card_eq_fintype_card, ← edgeFinset_card, Fintype.card_fin]
      using cycle_card_edges n
  simpa only [Fintype.card_fin] using spanningTreeCount_eq_card_edges
    (cycleGraph (n + 3)) hc (fun e => cycle_delete_connected n e.val e.property)

/-- The spanning-tree formula for every cycle of order at least three. -/
theorem cycle_spanningTreeCount_of_three_le (n : ℕ) (hn : 3 ≤ n) :
    spanningTreeCount (cycleGraph n) = n := by
  have heq : n = (n - 3) + 3 := by omega
  conv_lhs => rw [heq]
  rw [cycle_spanningTreeCount]
  omega


end Conjecture464
