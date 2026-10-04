import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Sym
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

/-!
# Finite matchings and the vertex-deletion recurrence

An edge is an unordered pair (`Sym2 V`). A matching on `S` is a finite set
of edges of `G`, with endpoints in `S`, such that two edges sharing an
endpoint are equal. Its cardinality counts edges, not saturated vertices.
-/

namespace Conjecture1227

variable {V : Type*} [DecidableEq V]

/-- A finite edge set is a matching of the graph induced on `S`. -/
def IsMatchingOn (G : SimpleGraph V) (S : Finset V) (M : Finset (Sym2 V)) : Prop :=
  (∀ e ∈ M, e ∈ G.edgeSet ∧ ∀ v ∈ e, v ∈ S) ∧
  ∀ e ∈ M, ∀ f ∈ M, ∀ v, v ∈ e → v ∈ f → e = f

/-- A vertex is saturated when it is an endpoint of an edge in the matching. -/
def Saturates (M : Finset (Sym2 V)) (v : V) : Prop := ∃ e ∈ M, v ∈ e

/-- Maximum means largest edge cardinality among all matchings on `S`. -/
def MaximumMatching (G : SimpleGraph V) (S : Finset V) (M : Finset (Sym2 V)) : Prop :=
  IsMatchingOn G S M ∧ ∀ N, IsMatchingOn G S N → N.card ≤ M.card

/-- Every maximum-cardinality matching saturates the specified vertex. -/
def Essential (G : SimpleGraph V) (S : Finset V) (v : V) : Prop :=
  ∀ M, MaximumMatching G S M → Saturates M v

omit [DecidableEq V] in
lemma matching_empty (G : SimpleGraph V) (S : Finset V) :
    IsMatchingOn G S ∅ := by
  simp [IsMatchingOn]

omit [DecidableEq V] in
lemma matching_mono {G : SimpleGraph V} {S T : Finset V} {M : Finset (Sym2 V)}
    (h : IsMatchingOn G S M) (hST : S ⊆ T) : IsMatchingOn G T M := by
  exact ⟨fun e he => ⟨(h.1 e he).1, fun v hv => hST ((h.1 e he).2 v hv)⟩, h.2⟩

lemma matching_erase_vertex {G : SimpleGraph V} {S : Finset V}
    {M : Finset (Sym2 V)} {v : V} (h : IsMatchingOn G S M)
    (hv : ¬ Saturates M v) : IsMatchingOn G (S.erase v) M := by
  refine ⟨?_, h.2⟩
  intro e he
  refine ⟨(h.1 e he).1, ?_⟩
  intro w hw
  refine Finset.mem_erase.mpr ⟨?_, (h.1 e he).2 w hw⟩
  intro hwv
  subst w
  exact hv ⟨e, he, hw⟩

omit [DecidableEq V] in
lemma matching_not_saturates_of_not_mem {G : SimpleGraph V} {S : Finset V}
    {M : Finset (Sym2 V)} {v : V} (h : IsMatchingOn G S M) (hv : v ∉ S) :
    ¬ Saturates M v := by
  rintro ⟨e, he, hve⟩
  exact hv ((h.1 e he).2 v hve)

lemma matching_erase_edge {G : SimpleGraph V} {S : Finset V}
    {M : Finset (Sym2 V)} {e : Sym2 V} {v : V}
    (h : IsMatchingOn G S M) (he : e ∈ M) (hv : v ∈ e) :
    IsMatchingOn G (S.erase v) (M.erase e) ∧ ¬ Saturates (M.erase e) v := by
  have hM : IsMatchingOn G S (M.erase e) := by
    refine ⟨fun f hf => h.1 f (Finset.mem_of_mem_erase hf), ?_⟩
    intro f hf g hg w hwf hwg
    exact h.2 f (Finset.mem_of_mem_erase hf) g (Finset.mem_of_mem_erase hg) w hwf hwg
  have hn : ¬ Saturates (M.erase e) v := by
    rintro ⟨f, hf, hvf⟩
    exact (Finset.mem_erase.mp hf).1 (h.2 f (Finset.mem_of_mem_erase hf) e he v hvf hv)
  exact ⟨matching_erase_vertex hM hn, hn⟩

lemma matching_insert_edge {G : SimpleGraph V} {S : Finset V}
    {M : Finset (Sym2 V)} {v w : V} (h : IsMatchingOn G S M)
    (hv : v ∈ S) (hw : w ∈ S) (ha : G.Adj v w)
    (hnv : ¬ Saturates M v) (hnw : ¬ Saturates M w) :
    IsMatchingOn G S (insert s(v, w) M) := by
  refine ⟨?_, ?_⟩
  · intro e he
    rcases Finset.mem_insert.mp he with rfl | he
    · exact ⟨ha, by
        intro x hx
        rcases Sym2.mem_iff.mp hx with rfl | rfl
        · exact hv
        · exact hw⟩
    · exact h.1 e he
  · intro e he f hf x hxe hxf
    rcases Finset.mem_insert.mp he with rfl | heM
    · rcases Finset.mem_insert.mp hf with rfl | hfM
      · rfl
      · rcases Sym2.mem_iff.mp hxe with rfl | rfl
        · exact (hnv ⟨f, hfM, hxf⟩).elim
        · exact (hnw ⟨f, hfM, hxf⟩).elim
    · rcases Finset.mem_insert.mp hf with rfl | hfM
      · rcases Sym2.mem_iff.mp hxf with rfl | rfl
        · exact (hnv ⟨e, heM, hxe⟩).elim
        · exact (hnw ⟨e, heM, hxe⟩).elim
      · exact h.2 e heM f hfM x hxe hxf

omit [DecidableEq V] in
lemma exists_maximum_matching (G : SimpleGraph V) (S : Finset V) :
    ∃ M, MaximumMatching G S M := by
  classical
  let candidates := S.sym2.powerset.filter (IsMatchingOn G S)
  have hm : ∅ ∈ candidates := by simp [candidates, matching_empty]
  obtain ⟨M, hM, hmax⟩ := candidates.exists_max_image Finset.card ⟨∅, hm⟩
  refine ⟨M, (Finset.mem_filter.mp hM).2, ?_⟩
  intro N hN
  apply hmax N
  refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr ?_, hN⟩
  intro e he
  exact Finset.mem_sym2_iff.mpr (hN.1 e he).2

/-- Essential vertices obey the same one-move recurrence as normal play. -/
theorem essential_recurrence (G : SimpleGraph V) (S : Finset V) (v : V)
    (hv : v ∈ S) :
    Essential G S v ↔ ∃ w ∈ S.erase v, G.Adj v w ∧ ¬ Essential G (S.erase v) w := by
  classical
  constructor
  · intro hE
    obtain ⟨M, hM⟩ := exists_maximum_matching G S
    obtain ⟨e, he, hve⟩ := hE M hM
    obtain ⟨w, rfl⟩ := Sym2.mem_iff_exists.mp hve
    have ha : G.Adj v w := (hM.1.1 s(v, w) he).1
    have hw : w ∈ S.erase v := Finset.mem_erase.mpr
      ⟨ha.ne.symm, (hM.1.1 s(v, w) he).2 w (Sym2.mem_mk_right v w)⟩
    have hN := matching_erase_edge hM.1 he (Sym2.mem_mk_left v w)
    have hnotw := (matching_erase_edge hM.1 he (Sym2.mem_mk_right v w)).2
    refine ⟨w, hw, ha, ?_⟩
    intro hEw
    apply hnotw (hEw (M.erase s(v, w)) ⟨hN.1, ?_⟩)
    intro L hL
    have hLS : IsMatchingOn G S L := matching_mono hL (Finset.erase_subset v S)
    have hle := hM.2 L hLS
    have hlt : L.card < M.card := by
      by_contra hn
      have heq : L.card = M.card := Nat.le_antisymm hle (Nat.le_of_not_gt hn)
      have hLmax : MaximumMatching G S L := ⟨hLS, fun N h => heq ▸ hM.2 N h⟩
      exact matching_not_saturates_of_not_mem hL (Finset.not_mem_erase v S) (hE L hLmax)
    have hc := Finset.card_erase_add_one he
    omega
  · rintro ⟨w, hw, ha, hnE⟩
    unfold Essential at hnE
    push_neg at hnE
    obtain ⟨N, hN, hnw⟩ := hnE
    have hNv : ¬ Saturates N v :=
      matching_not_saturates_of_not_mem hN.1 (Finset.not_mem_erase v S)
    have hNS := matching_mono hN.1 (Finset.erase_subset v S)
    have hK := matching_insert_edge hNS hv (Finset.mem_of_mem_erase hw) ha hNv hnw
    intro M hM
    by_contra hnM
    have hMerase := matching_erase_vertex hM.1 hnM
    have hle := hN.2 M hMerase
    have hge := hM.2 (insert s(v, w) N) hK
    have hedge : s(v, w) ∉ N := fun he => hNv ⟨s(v, w), he, Sym2.mem_mk_left v w⟩
    rw [Finset.card_insert_of_not_mem hedge] at hge
    omega

end Conjecture1227
