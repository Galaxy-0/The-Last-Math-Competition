import Mathlib

/-!
# Conjecture 00000002310 is false

Conjecture (literal text): the base size `b(G)` is the minimal size of a base (a set of points
with trivial pointwise stabilizer); the supremum of `b` over almost simple groups is `7`
(attained by an action of `Sp₈(2)`), and the exception table for `b ∈ {6, 7}` has exactly 3 groups.

The class in the text is all almost simple (permutation) groups; it is not restricted to
non-standard actions. We take the narrowest standard reading of that class: finite almost simple
groups acting faithfully and primitively on a finite set (dropping primitivity or finiteness only
enlarges the class). Then the natural action of `A_n` (`n ≥ 5`) on `n` points is in the class and has
base size exactly `n - 2`: any `n - 3` points leave three free points carrying a 3-cycle that fixes
them all, while an even permutation fixing `n - 2` points is the identity. Hence the supremum is
`⊤` (`conjecture_2310_false`); e.g. `A₁₀` has base size `8 > 7` (`conjecture_2310_false_A10`).
-/

namespace C2310

open Equiv MulAction Finset

/-- `B` is a base: only the identity fixes every point of `B`. -/
def IsBase (G : Type*) {Ω : Type*} [Group G] [MulAction G Ω] (B : Finset Ω) : Prop :=
  ∀ g : G, (∀ x ∈ B, g • x = x) → g = 1

/-- The base size `b(G)`: the minimal cardinality of a base. -/
noncomputable def baseSize (G Ω : Type*) [Group G] [MulAction G Ω] : ℕ :=
  sInf {n | ∃ B : Finset Ω, B.card = n ∧ IsBase G B}

/-- Almost simple: `G` has a nonabelian simple normal subgroup `T` with trivial centralizer,
i.e. `T ≅ Inn(T) ≤ G ≤ Aut(T)` via the conjugation action. -/
def IsAlmostSimple (G : Type*) [Group G] : Prop :=
  ∃ T : Subgroup G, T.Normal ∧ IsSimpleGroup T ∧ (∃ x y : T, x * y ≠ y * x) ∧
    Subgroup.centralizer (T : Set G) = ⊥

/-- Base sizes of finite almost simple groups acting faithfully and primitively on finite sets. -/
def almostSimpleBaseSizes : Set ℕ∞ :=
  {b | ∃ (G : Type) (_ : Group G) (Ω : Type) (_ : MulAction G Ω), Finite G ∧ Finite Ω ∧
    IsAlmostSimple G ∧ FaithfulSMul G Ω ∧ IsPreprimitive G Ω ∧ b = baseSize G Ω}

variable {α : Type} [Fintype α] [DecidableEq α]

lemma smul_eq (g : alternatingGroup α) (x : α) : g • x = (g : Perm α) x := rfl

/-- A set missing at least three points is not a base of `A_n`: a 3-cycle on three missing
points fixes it pointwise. -/
lemma not_isBase (B : Finset α) (hB : B.card + 3 ≤ Fintype.card α) :
    ¬ IsBase (alternatingGroup α) B := by
  have h3 : 2 < Bᶜ.card := by rw [card_compl]; omega
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := two_lt_card_iff.mp h3
  intro hbase
  have hσ : swap a b * swap b c ∈ alternatingGroup α := by
    simp [Perm.mem_alternatingGroup, Perm.sign_swap hab, Perm.sign_swap hbc]
  have h1 := hbase ⟨_, hσ⟩ (fun x hx => by
    have hxa : x ≠ a := fun h => (mem_compl.mp ha) (h ▸ hx)
    have hxb : x ≠ b := fun h => (mem_compl.mp hb) (h ▸ hx)
    have hxc : x ≠ c := fun h => (mem_compl.mp hc) (h ▸ hx)
    rw [smul_eq]
    simp [swap_apply_of_ne_of_ne hxb hxc, swap_apply_of_ne_of_ne hxa hxb])
  have h2 := congrArg (fun g : alternatingGroup α => (g : Perm α) c) h1
  simp at h2
  exact hac h2

/-- The complement of two points is a base of `A_n`: an even permutation moving at most two
points is the identity. -/
lemma isBase_compl_pair (a b : α) : IsBase (alternatingGroup α) ({a, b}ᶜ) := by
  intro g hg
  have hsupp : (g : Perm α).support ⊆ {a, b} := by
    intro x hx
    rw [Perm.mem_support] at hx
    by_contra h
    exact hx (by rw [← smul_eq]; exact hg x (mem_compl.mpr h))
  have hcard : (g : Perm α).support.card ≤ 2 := (card_le_card hsupp).trans card_le_two
  have hsign : Perm.sign (g : Perm α) = 1 := Perm.mem_alternatingGroup.mp g.2
  have hne := Perm.card_support_ne_one (g : Perm α)
  interval_cases h : (g : Perm α).support.card
  · exact Subtype.ext (Perm.support_eq_empty_iff.mp (card_eq_zero.mp h))
  · exact absurd rfl hne
  · rw [(Perm.card_support_eq_two.mp h).sign_eq] at hsign
    exact absurd hsign (by decide)

/-- The base size of `A_n` in its natural action on `n ≥ 2` points is exactly `n - 2`. -/
theorem baseSize_alternating (h : 2 ≤ Fintype.card α) :
    baseSize (alternatingGroup α) α = Fintype.card α - 2 := by
  obtain ⟨a, b, hab⟩ := Fintype.one_lt_card_iff.mp h
  have hc : ({a, b}ᶜ : Finset α).card = Fintype.card α - 2 := by
    rw [card_compl, card_pair hab]
  refine le_antisymm (Nat.sInf_le ⟨_, hc, isBase_compl_pair a b⟩)
    (le_csInf ⟨_, _, hc, isBase_compl_pair a b⟩ ?_)
  rintro m ⟨B, rfl, hB⟩
  by_contra hlt
  exact not_isBase B (by omega) hB

/-- `A_n` (`n ≥ 5`) is almost simple: it is a nonabelian simple group (take `T = ⊤`). -/
theorem isAlmostSimple_alternating (h : 5 ≤ Fintype.card α) :
    IsAlmostSimple (alternatingGroup α) := by
  have hs : IsSimpleGroup (alternatingGroup α) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card]; omega)
  obtain ⟨a, b, c, -, -, -, hab, hac, hbc⟩ :=
    two_lt_card_iff.mp (by rw [card_univ]; omega : 2 < (univ : Finset α).card)
  obtain ⟨d, hd⟩ : ({a, b, c}ᶜ : Finset α).Nonempty := by
    rw [← card_pos, card_compl]
    have := card_le_three (a := a) (b := b) (c := c)
    omega
  simp only [mem_compl, mem_insert, mem_singleton, not_or] at hd
  obtain ⟨hda, hdb, hdc⟩ := hd
  have hx : swap a b * swap a c ∈ alternatingGroup α := by
    simp [Perm.mem_alternatingGroup, Perm.sign_swap hab, Perm.sign_swap hac]
  have hy : swap a b * swap a d ∈ alternatingGroup α := by
    simp [Perm.mem_alternatingGroup, Perm.sign_swap hab, Perm.sign_swap (Ne.symm hda)]
  set x : alternatingGroup α := ⟨_, hx⟩
  set y : alternatingGroup α := ⟨_, hy⟩
  have hxy : x * y ≠ y * x := by
    intro he
    have := congrArg (fun g : alternatingGroup α => (g : Perm α) d) he
    simp [x, y, swap_apply_of_ne_of_ne hda hdc, swap_apply_of_ne_of_ne hda hdb,
      swap_apply_of_ne_of_ne (Ne.symm hab) hbc] at this
    exact hab this
  refine ⟨⊤, inferInstance, Subgroup.topEquiv.isSimpleGroup, ⟨⟨x, trivial⟩, ⟨y, trivial⟩,
    fun he => hxy (congrArg Subtype.val he)⟩, ?_⟩
  rw [Subgroup.coe_top, Subgroup.centralizer_univ]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (alternatingGroup α))
      inferInstance with
    h | h
  · exact h
  · exfalso
    have : x ∈ Subgroup.center (alternatingGroup α) := h ▸ Subgroup.mem_top x
    exact hxy ((Subgroup.mem_center_iff.mp this y).symm)

/-- The natural action of `A_n` (`n ≥ 5`) on `Fin n` lies in the class and has base size
`n - 2`. -/
theorem mem_almostSimpleBaseSizes (n : ℕ) (hn : 5 ≤ n) :
    ((n - 2 : ℕ) : ℕ∞) ∈ almostSimpleBaseSizes := by
  refine ⟨alternatingGroup (Fin n), inferInstance, Fin n, inferInstance, inferInstance,
    inferInstance, isAlmostSimple_alternating (by simpa using hn), inferInstance,
    alternatingGroup.isPreprimitive_of_three_le_card _ (by simp; omega), ?_⟩
  rw [baseSize_alternating (by simp; omega), Fintype.card_fin]

/-- **Main theorem.** The supremum of the base size over (finite, faithful, primitive) almost
simple groups is `⊤`, not `7`. -/
theorem conjecture_2310_false : sSup almostSimpleBaseSizes = ⊤ ∧ sSup almostSimpleBaseSizes ≠ 7 := by
  have htop : sSup almostSimpleBaseSizes = ⊤ := by
    refine sSup_eq_top.mpr fun b hb => ?_
    obtain ⟨N, rfl⟩ := ENat.ne_top_iff_exists.mp hb.ne
    refine ⟨((N + 5 - 2 : ℕ) : ℕ∞), mem_almostSimpleBaseSizes (N + 5) (by omega), ?_⟩
    exact_mod_cast (by omega : N < N + 5 - 2)
  exact ⟨htop, by rw [htop]; exact ENat.top_ne_natCast 7⟩

/-- Concretely: `A₁₀` in its natural primitive action on 10 points is almost simple with base
size `8 > 7`. -/
theorem conjecture_2310_false_A10 :
    IsAlmostSimple (alternatingGroup (Fin 10)) ∧ IsPreprimitive (alternatingGroup (Fin 10)) (Fin 10)
      ∧ baseSize (alternatingGroup (Fin 10)) (Fin 10) = 8 :=
  ⟨isAlmostSimple_alternating (by simp), alternatingGroup.isPreprimitive_of_three_le_card _
    (by simp), by rw [baseSize_alternating (by simp), Fintype.card_fin]⟩

end C2310
