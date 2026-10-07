import Mathlib

/-!
# Conjecture 00000004124: the least size of a ccc, non-Knaster poset is never `ℵ₂`

Conjecture: "The least cardinality of a poset separating ccc from the Knaster property is
aleph_2, and the smallest counterexample can be constructed by refining a Suslin tree."

We refute the first conjunct in ZFC (no extra axioms). If some poset is ccc but not Knaster,
then some poset of cardinality exactly `ℵ₁` is ccc but not Knaster; and every ccc, non-Knaster
poset is uncountable. So the set of cardinalities of ccc, non-Knaster posets is either empty
(e.g. under `MA_ℵ₁`) or has least element `ℵ₁`. In neither case is its least element, or its
`sInf`, equal to `ℵ₂`. We prove this for preorders, partial orders, and partial orders with a
greatest element.

Definitions (only `≤` is used):
* `p, q` are compatible if they have a common lower bound;
* an antichain is a set of pairwise incompatible (distinct) elements;
* ccc: every antichain is countable;
* Knaster (property K): every uncountable subset has an uncountable subset whose elements are
  pairwise compatible (a linked subset).
-/

open Cardinal Set

namespace Conjecture4124

universe u

section Defs

variable {P : Type*} [LE P]

/-- `p` and `q` are compatible: they have a common lower bound. -/
def Compat (p q : P) : Prop := ∃ r, r ≤ p ∧ r ≤ q

/-- An antichain: any two distinct members are incompatible. -/
def IsAntichainC (A : Set P) : Prop := A.Pairwise fun p q => ¬ Compat p q

/-- A linked set: any two distinct members are compatible. -/
def IsLinked (B : Set P) : Prop := B.Pairwise Compat

variable (P) in
/-- The countable chain condition: every antichain is countable. -/
def CCC : Prop := ∀ A : Set P, IsAntichainC A → A.Countable

variable (P) in
/-- The Knaster property (property K): every uncountable subset has an uncountable linked
subset. -/
def Knaster : Prop := ∀ A : Set P, ¬ A.Countable → ∃ B ⊆ A, ¬ B.Countable ∧ IsLinked B

end Defs

section Basic

variable {P : Type u} [LE P]

/-- The hierarchy: the Knaster property implies ccc (so "separating" can only mean ccc and
not Knaster). -/
theorem ccc_of_knaster (h : Knaster P) : CCC P := by
  intro A hA
  by_contra hc
  obtain ⟨B, hBA, hBc, hBl⟩ := h A hc
  have hnt : B.Nontrivial := by
    rw [← not_subsingleton_iff]
    exact fun hs => hBc hs.finite.countable
  obtain ⟨x, hx, y, hy, hxy⟩ := hnt
  exact hA (hBA hx) (hBA hy) hxy (hBl hx hy hxy)

/-- Equivalent form of ccc: every uncountable subset contains two distinct compatible
elements. -/
theorem ccc_iff : CCC P ↔ ∀ A : Set P, ¬ A.Countable → ∃ p ∈ A, ∃ q ∈ A, p ≠ q ∧ Compat p q := by
  constructor
  · intro h A hA
    by_contra hne
    exact hA (h A fun p hp q hq hpq hc => hne ⟨p, hp, q, hq, hpq, hc⟩)
  · intro h A hA
    by_contra hc
    obtain ⟨p, hp, q, hq, hpq, hc'⟩ := h A hc
    exact hA hp hq hpq hc'

/-- Countable posets are (vacuously) Knaster. -/
theorem knaster_of_countable [Countable P] : Knaster P :=
  fun A hA => absurd A.to_countable hA

/-- Every non-Knaster poset has cardinality at least `ℵ₁`. -/
theorem aleph_one_le_of_not_knaster (h : ¬ Knaster P) : ℵ₁ ≤ #P := by
  by_contra hlt
  rw [not_le, lt_aleph_one_iff, mk_le_aleph0_iff] at hlt
  exact h knaster_of_countable

end Basic

section Closure

variable {P : Type u} [LE P]

open Classical in
/-- A chosen common lower bound of `p` and `q` (junk value `p` if they are incompatible). -/
noncomputable def lb (p q : P) : P := if h : Compat p q then h.choose else p

theorem lb_spec {p q : P} (h : Compat p q) : lb p q ≤ p ∧ lb p q ≤ q := by
  simp only [lb, dif_pos h]
  exact h.choose_spec

/-- Stage `n` of the closure of `W` under `lb`. -/
def stage (W : Set P) : ℕ → Set P
  | 0 => W
  | n + 1 => stage W n ∪ image2 lb (stage W n) (stage W n)

/-- The closure of `W` under the choice of common lower bounds. -/
def lbClosure (W : Set P) : Set P := ⋃ n, stage W n

theorem stage_mono (W : Set P) : Monotone (stage W) :=
  monotone_nat_of_le_succ fun _ => subset_union_left

theorem subset_lbClosure (W : Set P) : W ⊆ lbClosure W :=
  subset_iUnion (stage W) 0

theorem lb_mem {W : Set P} {p q : P} (hp : p ∈ lbClosure W) (hq : q ∈ lbClosure W) :
    lb p q ∈ lbClosure W := by
  obtain ⟨m, hm⟩ := mem_iUnion.1 hp
  obtain ⟨n, hn⟩ := mem_iUnion.1 hq
  exact mem_iUnion.2 ⟨max m n + 1, Or.inr (mem_image2_of_mem
    (stage_mono W (le_max_left m n) hm) (stage_mono W (le_max_right m n) hn))⟩

theorem mk_stage_le {W : Set P} (hW : #W ≤ ℵ₁) : ∀ n, #(stage W n) ≤ ℵ₁
  | 0 => hW
  | n + 1 => by
    have h := mk_stage_le hW n
    have h1 : ℵ₀ ≤ ℵ₁ := aleph0_lt_aleph_one.le
    calc #(stage W (n + 1)) ≤ #(stage W n) + #(image2 lb (stage W n) (stage W n)) :=
          mk_union_le _ _
      _ ≤ ℵ₁ := add_le_of_le h1 h (mk_image2_le.trans (mul_le_of_le h1 h h))

theorem mk_lbClosure_le {W : Set P} (hW : #W ≤ ℵ₁) : #(lbClosure W) ≤ ℵ₁ := by
  have e : lbClosure W = ⋃ i : ULift.{u} ℕ, stage W i.down := by
    ext x
    simp only [lbClosure, mem_iUnion, ULift.exists]
  rw [e]
  have h1 : ℵ₀ ≤ ℵ₁ := aleph0_lt_aleph_one.le
  refine (mk_iUnion_le _).trans (mul_le_of_le h1 ?_ (ciSup_le' fun i => mk_stage_le hW _))
  simp

/-- In the closure, compatibility is the same as compatibility in `P`. -/
theorem compat_lbClosure_iff {W : Set P} (p q : lbClosure W) :
    Compat p q ↔ Compat (p : P) q := by
  constructor
  · rintro ⟨r, hrp, hrq⟩
    exact ⟨r, hrp, hrq⟩
  · intro h
    exact ⟨⟨lb p q, lb_mem p.2 q.2⟩, (lb_spec h).1, (lb_spec h).2⟩

/-- The closure of any set inside a ccc poset is ccc (with the induced order). -/
theorem ccc_lbClosure (hP : CCC P) (W : Set P) : CCC (lbClosure W) := by
  intro A hA
  have hc : (Subtype.val '' A).Countable := hP _ (by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hxy
    rw [← compat_lbClosure_iff]
    exact hA hx hy (fun h => hxy (congrArg _ h)))
  exact countable_of_injective_of_countable_image Subtype.val_injective.injOn hc

/-- A subposet containing an uncountable set without uncountable linked subsets is not
Knaster. -/
theorem not_knaster_of_subset {Q W : Set P} (hWQ : W ⊆ Q) (hW : ¬ W.Countable)
    (hWl : ∀ B ⊆ W, ¬ B.Countable → ¬ IsLinked B) : ¬ Knaster Q := by
  intro hK
  obtain ⟨B, hBA, hBc, hBl⟩ := hK (Subtype.val ⁻¹' W) (by
    intro hc
    apply hW
    have := hc.image Subtype.val
    rwa [Subtype.image_preimage_coe, inter_eq_right.2 hWQ] at this)
  refine hWl (Subtype.val '' B) (by rintro _ ⟨x, hx, rfl⟩; exact hBA hx) ?_ ?_
  · exact fun hc => hBc (countable_of_injective_of_countable_image Subtype.val_injective.injOn hc)
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hxy
    obtain ⟨r, h1, h2⟩ := hBl hx hy (fun h => hxy (congrArg _ h))
    exact ⟨r, h1, h2⟩

/-- **Key lemma.** If `P` is ccc and not Knaster, then for any `X ⊆ P` with `#X ≤ ℵ₁` there is
`Q ⊇ X` of cardinality exactly `ℵ₁` that, with the induced order, is ccc and not Knaster. -/
theorem exists_aleph_one (hP : CCC P) (hK : ¬ Knaster P) (X : Set P) (hX : #X ≤ ℵ₁) :
    ∃ Q : Set P, X ⊆ Q ∧ #Q = ℵ₁ ∧ CCC Q ∧ ¬ Knaster Q := by
  obtain ⟨A, hA, hAB⟩ : ∃ A : Set P, ¬ A.Countable ∧
      ∀ B ⊆ A, ¬ B.Countable → ¬ IsLinked B := by
    by_contra h
    apply hK
    intro A hA
    by_contra h'
    exact h ⟨A, hA, fun B hB hBc hBl => h' ⟨B, hB, hBc, hBl⟩⟩
  have hA1 : ℵ₁ ≤ #A := by
    rw [aleph_one_le_iff, ← not_le, le_aleph0_iff_set_countable]
    exact hA
  obtain ⟨W, hWA, hW⟩ := le_mk_iff_exists_subset.1 hA1
  have hWc : ¬ W.Countable := by
    rw [← le_aleph0_iff_set_countable, hW, not_le]
    exact aleph0_lt_aleph_one
  have h1 : ℵ₀ ≤ ℵ₁ := aleph0_lt_aleph_one.le
  have hWX : #(W ∪ X : Set P) ≤ ℵ₁ := (mk_union_le _ _).trans (add_le_of_le h1 hW.le hX)
  have hsub : W ⊆ lbClosure (W ∪ X) := subset_union_left.trans (subset_lbClosure _)
  refine ⟨lbClosure (W ∪ X), subset_union_right.trans (subset_lbClosure _), ?_,
    ccc_lbClosure hP _, not_knaster_of_subset hsub hWc fun B hB => hAB B (hB.trans hWA)⟩
  exact le_antisymm (mk_lbClosure_le hWX) (hW ▸ mk_le_mk_of_subset hsub)

end Closure

/-! ### The cardinalities of ccc, non-Knaster posets -/

/-- Cardinalities of ccc, non-Knaster partial orders (posets) in `Type u`. -/
def sepCards : Set Cardinal.{u} :=
  {κ | ∃ (P : Type u) (_ : PartialOrder P), CCC P ∧ ¬ Knaster P ∧ #P = κ}

/-- Cardinalities of ccc, non-Knaster preorders in `Type u`. -/
def sepCardsPre : Set Cardinal.{u} :=
  {κ | ∃ (P : Type u) (_ : Preorder P), CCC P ∧ ¬ Knaster P ∧ #P = κ}

/-- Cardinalities of ccc, non-Knaster partial orders with a greatest element in `Type u`. -/
def sepCardsTop : Set Cardinal.{u} :=
  {κ | ∃ (P : Type u) (_ : PartialOrder P) (_ : OrderTop P), CCC P ∧ ¬ Knaster P ∧ #P = κ}

/-- Abstract conclusion: a set of cardinals bounded below by `ℵ₁` that contains `ℵ₁` as soon as
it is nonempty has neither least element nor `sInf` equal to `ℵ₂`. -/
theorem not_aleph_two {S : Set Cardinal.{u}} (h1 : ∀ κ ∈ S, ℵ₁ ≤ κ)
    (h2 : S.Nonempty → ℵ₁ ∈ S) : ¬ IsLeast S (ℵ_ 2) ∧ sInf S ≠ ℵ_ 2 := by
  have hlt : ℵ₁ < ℵ_ 2 := aleph_lt_aleph.2 one_lt_two
  refine ⟨fun h => (h.2 (h2 ⟨_, h.1⟩)).not_gt hlt, ?_⟩
  rcases S.eq_empty_or_nonempty with hS | hS
  · rw [hS, Cardinal.sInf_empty]
    exact (aleph_pos 2).ne
  · rw [(IsLeast.csInf_eq ⟨h2 hS, h1⟩)]
    exact hlt.ne

theorem sepCards_spec :
    (∀ κ ∈ sepCards.{u}, ℵ₁ ≤ κ) ∧ (sepCards.{u}.Nonempty → ℵ₁ ∈ sepCards.{u}) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨P, _, -, hK, rfl⟩
    exact aleph_one_le_of_not_knaster hK
  · rintro ⟨_, P, _, hC, hK, -⟩
    obtain ⟨Q, -, hQ, hQC, hQK⟩ := exists_aleph_one hC hK ∅ (by simp)
    exact ⟨Q, inferInstance, hQC, hQK, hQ⟩

theorem sepCardsPre_spec :
    (∀ κ ∈ sepCardsPre.{u}, ℵ₁ ≤ κ) ∧ (sepCardsPre.{u}.Nonempty → ℵ₁ ∈ sepCardsPre.{u}) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨P, _, -, hK, rfl⟩
    exact aleph_one_le_of_not_knaster hK
  · rintro ⟨_, P, _, hC, hK, -⟩
    obtain ⟨Q, -, hQ, hQC, hQK⟩ := exists_aleph_one hC hK ∅ (by simp)
    exact ⟨Q, inferInstance, hQC, hQK, hQ⟩

theorem sepCardsTop_spec :
    (∀ κ ∈ sepCardsTop.{u}, ℵ₁ ≤ κ) ∧ (sepCardsTop.{u}.Nonempty → ℵ₁ ∈ sepCardsTop.{u}) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨P, _, _, -, hK, rfl⟩
    exact aleph_one_le_of_not_knaster hK
  · rintro ⟨_, P, _, _, hC, hK, -⟩
    obtain ⟨Q, hXQ, hQ, hQC, hQK⟩ := exists_aleph_one hC hK {⊤}
      (by rw [mk_singleton]; exact (one_lt_aleph0.trans aleph0_lt_aleph_one).le)
    exact ⟨Q, inferInstance, Subtype.orderTop (hXQ rfl), hQC, hQK, hQ⟩

/-- **Main theorem (conjecture 00000004124 is false).** For posets, preorders, and posets with a
greatest element (all in `Type u`): the least cardinality of a ccc, non-Knaster structure is not
`ℵ₂` (as `IsLeast`), and the `sInf` of these cardinalities is not `ℵ₂`. Moreover, whenever such
a structure exists, the least cardinality is `ℵ₁`. -/
theorem conjecture4124_false :
    (¬ IsLeast sepCards.{u} (ℵ_ 2) ∧ sInf sepCards.{u} ≠ ℵ_ 2) ∧
    (¬ IsLeast sepCardsPre.{u} (ℵ_ 2) ∧ sInf sepCardsPre.{u} ≠ ℵ_ 2) ∧
    (¬ IsLeast sepCardsTop.{u} (ℵ_ 2) ∧ sInf sepCardsTop.{u} ≠ ℵ_ 2) ∧
    (sepCards.{u}.Nonempty → IsLeast sepCards.{u} ℵ₁) ∧
    (sepCardsPre.{u}.Nonempty → IsLeast sepCardsPre.{u} ℵ₁) ∧
    (sepCardsTop.{u}.Nonempty → IsLeast sepCardsTop.{u} ℵ₁) :=
  ⟨not_aleph_two sepCards_spec.1 sepCards_spec.2,
   not_aleph_two sepCardsPre_spec.1 sepCardsPre_spec.2,
   not_aleph_two sepCardsTop_spec.1 sepCardsTop_spec.2,
   fun h => ⟨sepCards_spec.2 h, sepCards_spec.1⟩,
   fun h => ⟨sepCardsPre_spec.2 h, sepCardsPre_spec.1⟩,
   fun h => ⟨sepCardsTop_spec.2 h, sepCardsTop_spec.1⟩⟩

end Conjecture4124
