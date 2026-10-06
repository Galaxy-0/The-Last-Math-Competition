import Mathlib

/-!
# Conjecture 00000003526: well-founded trees, rank and ordinal height

A *tree* on a set `A` (descriptive set theory) is a nonempty set `T` of finite sequences of
elements of `A` such that every initial segment of a member of `T` is in `T`. A *branch* of `T`
is an infinite sequence all of whose finite initial segments lie in `T`; `T` is *well-founded*
when it has no branch.

The nodes of `T` are ordered by strict extension: `Ext T t s` means that `t` properly extends `s`.
A *descending chain* is a sequence of nodes `s₀ ⊊ s₁ ⊊ s₂ ⊊ ⋯`, each properly extending the
previous one. We prove:

* `treeWF_iff_no_descChain`, `no_descChain_iff_wf`: for a tree, having no branch, having no
  infinite descending chain, and well-foundedness of `Ext T` are equivalent;
* `nodeRank_eq_iSup_child`, `nodeRank_unique`: the rank of a node is
  `ρ(s) = sup {ρ(s⌢a) + 1 : s⌢a ∈ T}`, and it is the unique function with this recursion;
* `nodeRank_le_of_ranking`, `wf_iff_exists_ranking`: `ρ` is the least order-reversing map into
  the ordinals, and such a map exists iff `T` is well-founded;
* `ordHeight_eq_treeRank`: the ordinal height (the least `α` that bounds an order-reversing map
  of `T` into the ordinals) equals the rank of the tree `sup {ρ(s) + 1 : s ∈ T} = ρ(∅) + 1`;
* `ordinal_tree_realization`: every ordinal `α` is the root rank of a well-founded tree on the
  ordinals (strictly decreasing sequences below `α`), whose height is `α + 1`.
-/

namespace C3526

open Order Ordinal

universe u

variable {A : Type u}

/-- A tree on `A`: a nonempty set of finite sequences closed under initial segments. -/
def IsTree (T : Set (List A)) : Prop :=
  T.Nonempty ∧ ∀ t ∈ T, ∀ m < t.length, t.take m ∈ T

/-- The first `n` terms `⟨f 0, …, f (n-1)⟩` of an infinite sequence `f`. -/
def initSeg (f : ℕ → A) (n : ℕ) : List A := (List.range n).map f

/-- A branch of `T`: an infinite sequence all of whose finite initial segments are in `T`. -/
def IsBranch (T : Set (List A)) (f : ℕ → A) : Prop := ∀ n, initSeg f n ∈ T

/-- `T` is well-founded (as a tree) when it has no branch. -/
def TreeWF (T : Set (List A)) : Prop := ∀ f : ℕ → A, ¬ IsBranch T f

/-- The strict extension relation on the nodes of `T`: `Ext T t s` iff `t` properly extends `s`. -/
def Ext (T : Set (List A)) (t s : T) : Prop := s.1 <+: t.1 ∧ s.1 ≠ t.1

/-- `T` has an infinite descending chain `c 0 ⊊ c 1 ⊊ c 2 ⊊ ⋯` of nodes. -/
def HasDescChain (T : Set (List A)) : Prop := ∃ c : ℕ → T, ∀ n, Ext T (c (n + 1)) (c n)

variable {T : Set (List A)}

theorem IsTree.prefix_mem (hT : IsTree T) {s t : List A} (h : s <+: t) (ht : t ∈ T) : s ∈ T := by
  rcases (h.length_le).lt_or_eq with hlt | heq
  · rw [List.prefix_iff_eq_take.1 h]; exact hT.2 t ht _ hlt
  · rwa [h.eq_of_length heq]

theorem IsTree.nil_mem (hT : IsTree T) : [] ∈ T := by
  obtain ⟨t, ht⟩ := hT.1
  exact hT.prefix_mem (List.nil_prefix) ht

/-- The root `∅` of a tree. -/
def root (hT : IsTree T) : T := ⟨[], hT.nil_mem⟩

theorem initSeg_succ (f : ℕ → A) (n : ℕ) : initSeg f (n + 1) = initSeg f n ++ [f n] := by
  simp [initSeg, List.range_succ]

theorem length_initSeg (f : ℕ → A) (n : ℕ) : (initSeg f n).length = n := by simp [initSeg]

/-- A branch gives an infinite descending chain. -/
theorem descChain_of_branch {f : ℕ → A} (hf : IsBranch T f) : HasDescChain T := by
  refine ⟨fun n => ⟨initSeg f n, hf n⟩, fun n => ⟨?_, ?_⟩⟩
  · simp only [initSeg_succ]; exact List.prefix_append _ _
  · intro h
    have := congrArg List.length h
    simp [length_initSeg] at this

/-- An infinite descending chain gives a branch. -/
theorem branch_of_descChain (hT : IsTree T) (c : ℕ → T) (hc : ∀ n, Ext T (c (n + 1)) (c n)) :
    ∃ f : ℕ → A, IsBranch T f := by
  have mono : ∀ m n, m ≤ n → (c m).1 <+: (c n).1 := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => exact List.prefix_refl _
    | succ n _ ih => exact ih.trans (hc n).1
  have hlen : ∀ n, n ≤ (c n).1.length := by
    intro n
    induction n with
    | zero => exact Nat.zero_le _
    | succ n ih =>
      have h1 := (hc n).1.length_le
      have h2 : (c n).1.length ≠ (c (n + 1)).1.length := fun h => (hc n).2 ((hc n).1.eq_of_length h)
      omega
  let f : ℕ → A := fun k => (c (k + 1)).1[k]'(by have := hlen (k + 1); omega)
  refine ⟨f, fun n => hT.prefix_mem ?_ (c n).2⟩
  have key : initSeg f n = (c n).1.take n := by
    apply List.ext_getElem
    · simp [length_initSeg, hlen n]
    · intro i h1 h2
      simp only [initSeg, List.getElem_map, List.getElem_range, List.getElem_take, f]
      exact (mono (i + 1) n (by simp [length_initSeg] at h1; omega)).getElem _
  rw [key]; exact List.take_prefix _ _

/-- **(1a)** A tree is well-founded (has no branch) iff it has no infinite descending chain. -/
theorem treeWF_iff_no_descChain (hT : IsTree T) : TreeWF T ↔ ¬ HasDescChain T := by
  constructor
  · rintro h ⟨c, hc⟩
    obtain ⟨f, hf⟩ := branch_of_descChain hT c hc
    exact h f hf
  · intro h f hf
    exact h (descChain_of_branch hf)

/-- **(1b)** No infinite descending chain iff the strict extension relation is well-founded. -/
theorem no_descChain_iff_wf : ¬ HasDescChain T ↔ WellFounded (Ext T) := by
  rw [wellFounded_iff_isEmpty_descending_chain, HasDescChain, not_exists, isEmpty_subtype]

/-- The rank `ρ_T(s)` of a node: Mathlib's well-founded rank of `s` for `Ext T`
(junk value `0` if `T` is ill-founded). -/
noncomputable def nodeRank (T : Set (List A)) (s : T) : Ordinal.{u} :=
  open Classical in if h : WellFounded (Ext T) then (h.apply s).rank else 0

/-- The rank of the tree, `sup {ρ_T(s) + 1 : s ∈ T}`. -/
noncomputable def treeRank (T : Set (List A)) : Ordinal.{u} := ⨆ s : T, succ (nodeRank T s)

/-- An order-reversing map of the nodes into the ordinals: proper extensions get smaller values. -/
def IsRanking (T : Set (List A)) (φ : T → Ordinal.{u}) : Prop := ∀ s t, Ext T t s → φ t < φ s

/-- The ordinal height of `T`: the least `α` such that some order-reversing map
`T → Ordinal` takes all its values below `α` (`sInf ∅ = 0` if there is none). -/
noncomputable def ordHeight (T : Set (List A)) : Ordinal.{u} :=
  sInf {α | ∃ φ : T → Ordinal.{u}, IsRanking T φ ∧ ∀ s, φ s < α}

section WF

variable (hwf : WellFounded (Ext T))
include hwf

theorem nodeRank_eq_iSup_ext (s : T) :
    nodeRank T s = ⨆ t : {t : T // Ext T t s}, succ (nodeRank T t) := by
  simp only [nodeRank, dif_pos hwf]
  exact (hwf.apply s).rank_eq

theorem nodeRank_lt {s t : T} (h : Ext T t s) : nodeRank T t < nodeRank T s := by
  simp only [nodeRank, dif_pos hwf]
  exact Acc.rank_lt_of_rel _ h

/-- The rank is an order-reversing map. -/
theorem nodeRank_isRanking : IsRanking T (nodeRank T) := fun _ _ h => nodeRank_lt hwf h

theorem nodeRank_le_of_prefix {s t : T} (h : s.1 <+: t.1) : nodeRank T t ≤ nodeRank T s := by
  by_cases e : s.1 = t.1
  · rw [Subtype.ext e]
  · exact (nodeRank_lt hwf ⟨h, e⟩).le

/-- **(2a)** The rank recursion over one-step extensions:
`ρ_T(s) = sup {ρ_T(s⌢a) + 1 : s⌢a ∈ T}`. -/
theorem nodeRank_eq_iSup_child (hT : IsTree T) (s : T) :
    nodeRank T s = ⨆ a : {a : A // s.1 ++ [a] ∈ T}, succ (nodeRank T ⟨s.1 ++ [a.1], a.2⟩) := by
  apply le_antisymm
  · rw [nodeRank_eq_iSup_ext hwf]
    refine Ordinal.iSup_le fun ⟨t, hts⟩ => ?_
    obtain ⟨u, hu⟩ := hts.1
    cases u with
    | nil => exact absurd (by simpa using hu) hts.2
    | cons a w =>
      have hp : s.1 ++ [a] <+: t.1 := ⟨w, by rw [← hu]; simp⟩
      have hm : s.1 ++ [a] ∈ T := hT.prefix_mem hp t.2
      refine le_trans (succ_le_succ (nodeRank_le_of_prefix hwf (t := t) (s := ⟨_, hm⟩) hp)) ?_
      exact Ordinal.le_iSup (fun a : {a : A // s.1 ++ [a] ∈ T} =>
        succ (nodeRank T ⟨s.1 ++ [a.1], a.2⟩)) ⟨a, hm⟩
  · refine Ordinal.iSup_le fun a => succ_le_of_lt (nodeRank_lt hwf ⟨List.prefix_append _ _, ?_⟩)
    intro h; have := congrArg List.length h; simp at this

/-- **(2b)** The rank is the unique function satisfying the one-step recursion. -/
theorem nodeRank_unique (hT : IsTree T) (φ : T → Ordinal.{u})
    (hφ : ∀ s, φ s = ⨆ a : {a : A // s.1 ++ [a] ∈ T}, succ (φ ⟨s.1 ++ [a.1], a.2⟩)) :
    φ = nodeRank T := by
  funext s
  induction s using hwf.induction with
  | _ s ih =>
    rw [hφ, nodeRank_eq_iSup_child hwf hT]
    congr 1; funext a; congr 1
    exact ih _ ⟨List.prefix_append _ _, fun h => by have := congrArg List.length h; simp at this⟩

/-- **(2c)** The rank is the least order-reversing map into the ordinals. -/
theorem nodeRank_le_of_ranking (φ : T → Ordinal.{u}) (hφ : IsRanking T φ) (s : T) :
    nodeRank T s ≤ φ s := by
  induction s using hwf.induction with
  | _ s ih =>
    rw [nodeRank_eq_iSup_ext hwf]
    exact Ordinal.iSup_le fun t => succ_le_of_lt ((ih t.1 t.2).trans_lt (hφ s t.1 t.2))

/-- **(2d)** The rank of the tree is `ρ_T(∅) + 1`. -/
theorem treeRank_eq_succ_root (hT : IsTree T) : treeRank T = succ (nodeRank T (root hT)) := by
  apply le_antisymm
  · exact Ordinal.iSup_le fun s => succ_le_succ (nodeRank_le_of_prefix hwf List.nil_prefix)
  · exact Ordinal.le_iSup (fun s : T => succ (nodeRank T s)) (root hT)

/-- **(2e)** The ordinal height of a well-founded tree equals its rank `sup {ρ_T(s) + 1}`. -/
theorem ordHeight_eq_treeRank : ordHeight T = treeRank T := by
  apply le_antisymm
  · refine csInf_le' ⟨nodeRank T, nodeRank_isRanking hwf, fun s => ?_⟩
    exact (lt_succ _).trans_le (Ordinal.le_iSup (fun s : T => succ (nodeRank T s)) s)
  · refine le_csInf ⟨treeRank T, nodeRank T, nodeRank_isRanking hwf, fun s =>
      (lt_succ _).trans_le (Ordinal.le_iSup (fun s : T => succ (nodeRank T s)) s)⟩ ?_
    rintro α ⟨φ, hφ, hlt⟩
    exact Ordinal.iSup_le fun s => succ_le_of_lt ((nodeRank_le_of_ranking hwf φ hφ s).trans_lt (hlt s))

end WF

/-- An order-reversing map into the ordinals exists iff `Ext T` is well-founded. -/
theorem wf_iff_exists_ranking : WellFounded (Ext T) ↔ ∃ φ : T → Ordinal.{u}, IsRanking T φ := by
  constructor
  · exact fun hwf => ⟨nodeRank T, nodeRank_isRanking hwf⟩
  · rintro ⟨φ, hφ⟩
    exact Subrelation.wf (fun {t s} h => hφ s t h) (InvImage.wf φ Ordinal.lt_wf)

/-! ### Every ordinal is the root rank of a well-founded tree on the ordinals -/

/-- The tree on the ordinals of strictly decreasing sequences `α > s₀ > s₁ > ⋯ > s_k`. -/
def decTree (α : Ordinal.{u}) : Set (List Ordinal.{u}) := {s | (α :: s).IsChain (· > ·)}

/-- The last entry of `α :: s` (the bound for the next entry). -/
def bound (α : Ordinal.{u}) (s : List Ordinal.{u}) : Ordinal.{u} :=
  (α :: s).getLast (List.cons_ne_nil _ _)

theorem decTree_isTree (α : Ordinal.{u}) : IsTree (decTree α) := by
  refine ⟨⟨[], List.isChain_singleton _⟩, fun t ht m _ => ?_⟩
  have := List.IsChain.take ht (m + 1)
  simpa [decTree] using this

theorem append_mem_decTree {α : Ordinal.{u}} {s : List Ordinal.{u}} {a : Ordinal.{u}} :
    s ++ [a] ∈ decTree α ↔ s ∈ decTree α ∧ a < bound α s := by
  have : α :: (s ++ [a]) = (α :: s) ++ [a] := rfl
  simp only [decTree, Set.mem_ofPred_eq, this, List.isChain_append, bound,
    List.getLast?_eq_some_getLast (List.cons_ne_nil α s)]
  simp

theorem bound_append (α : Ordinal.{u}) (s : List Ordinal.{u}) (a : Ordinal.{u}) :
    bound α (s ++ [a]) = a := by
  have : α :: (s ++ [a]) = (α :: s) ++ [a] := rfl
  simp only [bound, this, List.getLast_append_singleton]

theorem bound_lt_of_append {α : Ordinal.{u}} :
    ∀ (w s : List Ordinal.{u}), w ≠ [] → s ++ w ∈ decTree α → bound α (s ++ w) < bound α s
  | [], _, h, _ => absurd rfl h
  | a :: w, s, _, hm => by
    have e : s ++ a :: w = (s ++ [a]) ++ w := by simp
    rw [e] at hm ⊢
    have ha := (append_mem_decTree.1 ((decTree_isTree α).prefix_mem (List.prefix_append _ _) hm)).2
    rcases eq_or_ne w [] with rfl | hw
    · simpa [bound_append] using ha
    · exact (bound_lt_of_append w _ hw hm).trans (by rwa [bound_append])

/-- `decTree α` is well-founded: `s ↦ bound α s` is an order-reversing map. -/
theorem decTree_wf (α : Ordinal.{u}) : WellFounded (Ext (decTree α)) := by
  refine wf_iff_exists_ranking.2 ⟨fun s => lift.{u + 1} (bound α s.1), fun s t h => ?_⟩
  obtain ⟨w, hw⟩ := h.1
  have hne : w ≠ [] := by rintro rfl; exact h.2 (by simpa using hw)
  have hm : s.1 ++ w ∈ decTree α := hw ▸ t.2
  simp only [← hw, lift_lt]
  exact bound_lt_of_append w s.1 hne hm

/-- **(3)** The rank of a node `s` of `decTree α` is its last entry (`α` at the root). -/
theorem nodeRank_decTree (α : Ordinal.{u}) (s : decTree α) :
    nodeRank (decTree α) s = lift.{u + 1} (bound α s.1) := by
  refine (congrFun (nodeRank_unique (decTree_wf α) (decTree_isTree α)
    (fun s => lift.{u + 1} (bound α s.1)) fun s => ?_) s).symm
  simp only [bound_append]
  apply le_antisymm
  · refine le_of_forall_lt fun c hc => ?_
    obtain ⟨c', rfl⟩ := Ordinal.mem_range_lift_of_le hc.le
    have hc' : c' < bound α s.1 := lift_lt.1 hc
    have hm : s.1 ++ [c'] ∈ decTree α := append_mem_decTree.2 ⟨s.2, hc'⟩
    exact (lt_succ _).trans_le (Ordinal.le_iSup
      (fun a : {a : Ordinal.{u} // s.1 ++ [a] ∈ decTree α} => succ (lift.{u + 1} a.1)) ⟨c', hm⟩)
  · exact Ordinal.iSup_le fun a => succ_le_of_lt (lift_lt.2 (append_mem_decTree.1 a.2).2)

/-- **(3')** Every ordinal `α` is realized: `decTree α` is a well-founded tree on the ordinals
with root rank `α` and ordinal height `α + 1`. -/
theorem ordinal_tree_realization (α : Ordinal.{u}) :
    IsTree (decTree α) ∧ TreeWF (decTree α) ∧
      nodeRank (decTree α) (root (decTree_isTree α)) = lift.{u + 1} α ∧
      ordHeight (decTree α) = succ (lift.{u + 1} α) := by
  have hroot : nodeRank (decTree α) (root (decTree_isTree α)) = lift.{u + 1} α := by
    rw [nodeRank_decTree]; rfl
  refine ⟨decTree_isTree α, (treeWF_iff_no_descChain (decTree_isTree α)).2
    (no_descChain_iff_wf.2 (decTree_wf α)), hroot, ?_⟩
  rw [ordHeight_eq_treeRank (decTree_wf α), treeRank_eq_succ_root (decTree_wf α) (decTree_isTree α), hroot]

/-- **Main theorem.** For a tree `T` on any set `A` (in particular on the ordinals):
no branch ⟺ no infinite descending chain ⟺ `Ext T` is well-founded ⟺ `T` has an ordinal ranking;
and when `T` is well-founded its rank function satisfies the one-step recursion, is the least
ranking, and the ordinal height of `T` equals `sup {ρ_T(s) + 1 : s ∈ T} = ρ_T(∅) + 1`. -/
theorem tree_wf_rank_height (hT : IsTree T) :
    (TreeWF T ↔ ¬ HasDescChain T) ∧ (¬ HasDescChain T ↔ WellFounded (Ext T)) ∧
    (WellFounded (Ext T) ↔ ∃ φ : T → Ordinal.{u}, IsRanking T φ) ∧
    (WellFounded (Ext T) →
      (∀ s : T, nodeRank T s =
        ⨆ a : {a : A // s.1 ++ [a] ∈ T}, succ (nodeRank T ⟨s.1 ++ [a.1], a.2⟩)) ∧
      (∀ φ : T → Ordinal.{u}, IsRanking T φ → ∀ s, nodeRank T s ≤ φ s) ∧
      ordHeight T = treeRank T ∧ treeRank T = succ (nodeRank T (root hT))) :=
  ⟨treeWF_iff_no_descChain hT, no_descChain_iff_wf, wf_iff_exists_ranking, fun hwf =>
    ⟨nodeRank_eq_iSup_child hwf hT, nodeRank_le_of_ranking hwf, ordHeight_eq_treeRank hwf,
      treeRank_eq_succ_root hwf hT⟩⟩

/-! ### Second reading: set-theoretic trees `(P, <)` -/

/-- A set-theoretic tree: a partial order in which `{s : s < t}` is well-ordered for every `t`. -/
class IsSetTree (P : Type u) [PartialOrder P] : Prop where
  wo : ∀ t : P, IsWellOrder (Set.Iio t) (· < ·)

variable {P : Type u} [PartialOrder P] [IsSetTree P]

instance (t : P) : IsWellOrder (Set.Iio t) (· < ·) := IsSetTree.wo t

/-- The height (level) of `t`: the order type of `{s : s < t}`. -/
noncomputable def ht (t : P) : Ordinal.{u} := Ordinal.type ((· < ·) : Set.Iio t → Set.Iio t → Prop)

/-- The height of the tree: the least ordinal greater than the height of every element. -/
noncomputable def setTreeHeight (P : Type u) [PartialOrder P] [IsSetTree P] : Ordinal.{u} :=
  sInf {α | ∀ t : P, ht t < α}

/-- In a set-theoretic tree descending chains vanish: `<` is well-founded. -/
theorem setTree_wf : WellFounded ((· < ·) : P → P → Prop) := by
  refine wellFounded_iff_isEmpty_descending_chain.2 ⟨fun ⟨f, hf⟩ => ?_⟩
  have h0 : ∀ n, f (n + 1) < f 0 := fun n => by
    induction n with
    | zero => exact hf 0
    | succ n ih => exact (hf (n + 1)).trans ih
  exact (wellFounded_iff_isEmpty_descending_chain.1
    (IsWellFounded.wf (r := ((· < ·) : Set.Iio (f 0) → Set.Iio (f 0) → Prop)))).false
    ⟨fun n => ⟨f (n + 1), h0 n⟩, fun n => hf (n + 1)⟩

/-- The well-founded rank of `t` for `<`. -/
noncomputable def setRank (t : P) : Ordinal.{u} := (setTree_wf.apply t).rank

theorem ht_eq_typein {s t : P} (h : s < t) :
    ht s = Ordinal.typein ((· < ·) : Set.Iio t → Set.Iio t → Prop) ⟨s, h⟩ := by
  rw [← Ordinal.type_subrel]
  exact Ordinal.type_eq.2 ⟨{
    toFun := fun z => ⟨⟨z.1, z.2.trans h⟩, z.2⟩
    invFun := fun b => ⟨b.1.1, b.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_rel_iff' := Iff.rfl }⟩

/-- **(B)** The well-founded rank of every node is its height. -/
theorem setRank_eq_ht (t : P) : setRank t = ht t := by
  refine (setTree_wf (P := P)).induction (C := fun t => setRank t = ht t) t fun t ih => ?_
  · have e : ∀ b : {b // b < t}, setRank b.1 =
        Ordinal.typein ((· < ·) : Set.Iio t → Set.Iio t → Prop) ⟨b.1, b.2⟩ :=
      fun b => (ih b.1 b.2).trans (ht_eq_typein b.2)
    have hr : setRank t = ⨆ b : {b // b < t}, succ (setRank b.1) := (setTree_wf.apply t).rank_eq
    rw [hr]
    apply le_antisymm
    · exact Ordinal.iSup_le fun b => succ_le_of_lt ((e b).trans_lt (Ordinal.typein_lt_type _ _))
    · refine le_of_forall_lt fun c hc => ?_
      obtain ⟨a, rfl⟩ := Ordinal.typein_surj _ hc
      rw [← e ⟨a.1, a.2⟩]
      exact (lt_succ _).trans_le
        (Ordinal.le_iSup (fun b : {b // b < t} => succ (setRank b.1)) ⟨a.1, a.2⟩)

/-- **(B')** The rank of the well-founded order, `sup {rank t + 1}`, is the height of the tree. -/
theorem setTreeHeight_eq_rank : setTreeHeight P = ⨆ t : P, succ (setRank t) := by
  have hlt : ∀ t : P, ht t < ⨆ t : P, succ (setRank t) := fun t => by
    rw [← setRank_eq_ht]
    exact (lt_succ _).trans_le (Ordinal.le_iSup (fun t : P => succ (setRank t)) t)
  apply le_antisymm
  · exact csInf_le' hlt
  · refine le_csInf ⟨_, hlt⟩ fun α hα => ?_
    exact Ordinal.iSup_le fun t => succ_le_of_lt (by rw [setRank_eq_ht]; exact hα t)

/-- **Main theorem, set-theoretic reading.** -/
theorem setTree_wf_rank_height :
    WellFounded ((· < ·) : P → P → Prop) ∧ (∀ t : P, setRank t = ht t) ∧
      setTreeHeight P = ⨆ t : P, succ (setRank t) :=
  ⟨setTree_wf, setRank_eq_ht, setTreeHeight_eq_rank⟩

end C3526
