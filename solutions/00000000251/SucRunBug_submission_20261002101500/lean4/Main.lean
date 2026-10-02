import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
noncomputable section
open scoped Topology
namespace TLMC251
abbrev tree : SimpleGraph (Fin 2) := ⊤
theorem tree_is_tree : tree.IsTree := by
  rw [SimpleGraph.isTree_iff_connected_and_card]
  refine ⟨SimpleGraph.connected_top, ?_⟩
  rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card]
  change (⊤ : SimpleGraph (Fin 2)).edgeFinset.card + 1 = Nat.card (Fin 2)
  rw [SimpleGraph.card_edgeFinset_top_eq_card_choose_two]
  norm_num [Nat.card_eq_fintype_card]
theorem edge_count : tree.edgeFinset.card = 1 := by
  change (⊤ : SimpleGraph (Fin 2)).edgeFinset.card = 1
  rw [SimpleGraph.card_edgeFinset_top_eq_card_choose_two]
  norm_num

theorem no_injective_labeling : ¬ ∃ f : Fin 2 → ZMod 1, Function.Injective f := by
  rintro ⟨f, hf⟩
  have heq : f 0 = f 1 := Subsingleton.elim _ _
  exact (by decide : (0 : Fin 2) ≠ 1) (hf heq)
#print axioms tree_is_tree
#print axioms edge_count
#print axioms no_injective_labeling
end TLMC251
