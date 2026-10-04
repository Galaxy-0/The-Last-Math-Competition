import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Tactic

open SimpleGraph
namespace Conjecture464

private theorem path_not_wrap (n : ℕ) :
    ¬ (pathGraph (n+3)).Adj (-1) 0 := by
  simp [pathGraph_adj, Fin.coe_neg_one]

private theorem cycle_delete_predecessor_connected (n : ℕ) (d : Fin (n+3)) :
    ((cycleGraph (n+3)).deleteEdges {s(d-1,d)}).Connected := by
  let f : pathGraph (n+3) →g (cycleGraph (n+3)).deleteEdges {s(d-1,d)} := {
    toFun := fun x => x + d
    map_rel' := by
      intro x y hxy
      apply deleteEdges_adj.mpr
      constructor
      · apply (circulantGraph_adj_translate (d := d)).mpr
        exact pathGraph_le_cycleGraph hxy
      · simp only [Set.mem_singleton_iff, Sym2.eq_iff]
        rintro (⟨hx,hy⟩ | ⟨hx,hy⟩)
        · have hx' : x = -1 := by
            apply add_right_cancel (b := d)
            simpa [sub_eq_add_neg, add_comm] using hx
          have hy' : y = 0 := by
            apply add_right_cancel (b := d)
            simpa using hy
          subst x; subst y
          exact path_not_wrap n hxy
        · have hx' : x = 0 := by
            apply add_right_cancel (b := d)
            simpa using hx
          have hy' : y = -1 := by
            apply add_right_cancel (b := d)
            simpa [sub_eq_add_neg, add_comm] using hy
          subst x; subst y
          exact path_not_wrap n hxy.symm }
  apply Connected.map f ?_ (pathGraph_connected (n+2))
  intro y
  refine ⟨y-d, ?_⟩
  change y-d+d=y
  exact sub_add_cancel y d

/-- Removing any edge of a cycle with at least three vertices leaves a connected graph. -/
theorem cycle_delete_connected (n : ℕ) (e : Sym2 (Fin (n+3)))
    (he : e ∈ (cycleGraph (n+3)).edgeSet) :
    ((cycleGraph (n+3)).deleteEdges {e}).Connected := by
  induction e using Sym2.ind with
  | _ u v =>
    have huv : (cycleGraph (n+3)).Adj u v := he
    rcases cycleGraph_adj.mp huv with h | h
    · have hu : u = v + 1 := by simpa [add_comm] using (sub_eq_iff_eq_add.mp h)
      have heq : s(u,v) = s(u-1,u) := by rw [hu]; simp [Sym2.eq_swap]
      rw [heq]
      exact cycle_delete_predecessor_connected n u
    · have hv : v = u + 1 := by simpa [add_comm] using (sub_eq_iff_eq_add.mp h)
      have heq : s(u,v) = s(v-1,v) := by rw [hv]; simp
      rw [heq]
      exact cycle_delete_predecessor_connected n v

end Conjecture464
