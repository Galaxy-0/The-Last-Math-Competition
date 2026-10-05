import Mathlib

/-!
# Conjecture 00000002591: the Dedekind–MacNeille bound `2^|P|` is not attained for `|P| ≥ 3`

The conjecture asserts, among other things, that the number of isomorphism types of finite
posets `P` with `|DM(P)| = 2^|P|` is superpolynomial (in `n = |P|`). We show that no poset
with `n ≥ 3` elements attains the bound, so this number is `0` for every `n ≥ 3`.

`DM(P)` is Mathlib's `DedekindCut P = Concept P P (· ≤ ·)`: pairs `(A, B)` of subsets with
`upperBounds A = B` and `lowerBounds B = A`. Such a cut is determined by `A`, and the possible
`A` are exactly the sets with `lowerBounds (upperBounds A) = A` (`exists_cut_iff`). The empty
set is the left set of a cut iff `P` has no least element; `P` itself is always one.

Argument: if all `2^n` subsets were left sets of cuts, then `{x}` closed forces `Iic x = {x}`
(an antichain), and then a two-element set `{x, y}` has no upper bound, so its closure is all
of `P`; hence `n ≤ 2`. The argument uses only sets with one or two elements, so it also shows
that some nonempty proper subset is not a cut (`exists_proper_not_cut`).
-/

namespace Conjecture2591

open Set Filter

section General

variable {α : Type*} [PartialOrder α]

/-- A set is the left set of a Dedekind cut iff it equals the lower bounds of its upper
bounds. -/
theorem exists_cut_iff (s : Set α) :
    (∃ c : DedekindCut α, c.left = s) ↔ lowerBounds (upperBounds s) = s := by
  constructor
  · rintro ⟨c, rfl⟩
    rw [c.upperBounds_left, c.lowerBounds_right]
  · intro h
    exact ⟨⟨s, upperBounds s, rfl, h⟩, rfl⟩

/-- If every singleton and every two-element set is the left set of a cut, then `α` has no
three pairwise distinct elements. -/
theorem no_three_of_cuts
    (h1 : ∀ x : α, ∃ c : DedekindCut α, c.left = {x})
    (h2 : ∀ x y : α, ∃ c : DedekindCut α, c.left = {x, y}) (x y z : α) :
    x = y ∨ x = z ∨ y = z := by
  -- singletons closed: `Iic u = {u}`
  have hI : ∀ u : α, Iic u = {u} := fun u => by
    have e : lowerBounds (Ici u) = Iic u := by
      ext w
      exact ⟨fun hw => hw (mem_Ici.2 le_rfl), fun hw v hv => le_trans hw hv⟩
    have := (exists_cut_iff _).1 (h1 u)
    rwa [upperBounds_singleton, e] at this
  by_contra hne
  push Not at hne
  obtain ⟨hxy, hxz, hyz⟩ := hne
  -- `{x, y}` has no upper bound
  have hU : upperBounds ({x, y} : Set α) = ∅ := by
    ext u
    simp only [mem_upperBounds, mem_insert_iff, mem_singleton_iff, forall_eq_or_imp,
      forall_eq, mem_empty_iff_false, iff_false, not_and]
    intro hx hy
    have hx' : x ∈ Iic u := hx
    have hy' : y ∈ Iic u := hy
    rw [hI u, mem_singleton_iff] at hx' hy'
    exact hxy (hx'.trans hy'.symm)
  -- so its closure is everything, but `z ∉ {x, y}`
  have hcl := (exists_cut_iff _).1 (h2 x y)
  rw [hU] at hcl
  have hz : z ∈ ({x, y} : Set α) := by rw [← hcl]; simp
  rcases hz with h | h
  · exact hxz h.symm
  · exact hyz (mem_singleton_iff.1 h).symm

variable [Fintype α]

/-- With at least three elements, some nonempty proper subset (of size one or two) is not the
left set of any cut. -/
theorem exists_proper_not_cut (h : 3 ≤ Fintype.card α) :
    ∃ s : Set α, s.Nonempty ∧ s ≠ univ ∧ ∀ c : DedekindCut α, c.left ≠ s := by
  obtain ⟨x, y, z, hxy, hxz, hyz⟩ := Fintype.two_lt_card_iff.1 h
  by_cases h1 : ∀ u : α, ∃ c : DedekindCut α, c.left = {u}
  · by_cases h2 : ∀ u v : α, ∃ c : DedekindCut α, c.left = {u, v}
    · rcases no_three_of_cuts h1 h2 x y z with h | h | h
      exacts [absurd h hxy, absurd h hxz, absurd h hyz]
    · push Not at h2
      obtain ⟨u, v, huv⟩ := h2
      refine ⟨{u, v}, insert_nonempty _ _, fun hU => ?_, huv⟩
      have hx : x ∈ ({u, v} : Set α) := hU ▸ mem_univ x
      have hy : y ∈ ({u, v} : Set α) := hU ▸ mem_univ y
      have hz : z ∈ ({u, v} : Set α) := hU ▸ mem_univ z
      simp only [mem_insert_iff, mem_singleton_iff] at hx hy hz
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> rcases hz with rfl | rfl <;>
        simp_all
  · push Not at h1
    obtain ⟨u, hu⟩ := h1
    refine ⟨{u}, singleton_nonempty u, fun hU => ?_, hu⟩
    have hx : x ∈ ({u} : Set α) := hU ▸ mem_univ x
    have hy : y ∈ ({u} : Set α) := hU ▸ mem_univ y
    exact hxy ((mem_singleton_iff.1 hx).trans (mem_singleton_iff.1 hy).symm)

/-- The size law `|DM(P)| ≤ 2^|P|` (true). -/
theorem card_cuts_le : Nat.card (DedekindCut α) ≤ 2 ^ Fintype.card α := by
  classical
  rw [← Fintype.card_set, ← Nat.card_eq_fintype_card]
  exact Nat.card_le_card_of_injective _ Concept.extent_injective

/-- For `|P| ≥ 3` the bound is never attained: `|DM(P)| < 2^|P|`. (In particular no antichain
with at least three elements attains it.) -/
theorem card_cuts_lt (h : 3 ≤ Fintype.card α) :
    Nat.card (DedekindCut α) < 2 ^ Fintype.card α := by
  classical
  obtain ⟨s, -, -, hs⟩ := exists_proper_not_cut h
  have : Fintype (DedekindCut α) := Fintype.ofInjective _ Concept.extent_injective
  rw [Nat.card_eq_fintype_card, ← Fintype.card_set]
  exact Fintype.card_lt_of_injective_of_notMem _ Concept.extent_injective (b := s)
    (by rintro ⟨c, hc⟩; exact hs c hc)

end General

/-! ## Counting the posets that attain the bound -/

/-- Partial orders on `Fin n` whose Dedekind–MacNeille completion has at least `2 ^ n`
elements (equivalently, by `card_cuts_le`, exactly `2 ^ n`). -/
def Attaining (n : ℕ) : Type :=
  {P : PartialOrder (Fin n) // 2 ^ n ≤ Nat.card (@DedekindCut (Fin n) P.toPreorder)}

/-- Order-isomorphism of two such partial orders. -/
def Iso {n : ℕ} (P Q : Attaining n) : Prop :=
  Nonempty (@OrderIso (Fin n) (Fin n) P.1.toLE Q.1.toLE)

/-- `E n`: the number of isomorphism types of `n`-element posets attaining the bound. -/
noncomputable def E (n : ℕ) : ℕ := Nat.card (Quot (@Iso n))

/-- There are only finitely many partial orders on `Fin n`, so `E n` is a genuine count. -/
instance (n : ℕ) : Finite (PartialOrder (Fin n)) :=
  Finite.of_injective (fun P : PartialOrder (Fin n) => P.le) fun P Q h =>
    PartialOrder.ext fun x y => by rw [show P.le = Q.le from h]

instance (n : ℕ) : Finite (Attaining n) := Subtype.finite

/-- In a poset whose order is equality and in which every element has a unique "other"
element (a two-element antichain), every subset is the left set of a cut. -/
theorem card_set_le_of_antichain_two {β : Type*} [PartialOrder β] [Finite β]
    (hanti : ∀ a b : β, a ≤ b → a = b) (hother : ∀ w : β, ∃ v, v ≠ w ∧ ∀ a, a ≠ w → a = v) :
    Nat.card (Set β) ≤ Nat.card (DedekindCut β) := by
  have hs : Function.Surjective (fun c : DedekindCut β => c.left) := fun s => by
    refine (exists_cut_iff s).2
      (Subset.antisymm (fun w hw => ?_) (subset_lowerBounds_upperBounds s))
    by_contra hws
    obtain ⟨v, hvw, hv⟩ := hother w
    have hub : v ∈ upperBounds s := fun a ha => le_of_eq (hv a fun h => hws (h ▸ ha))
    exact hvw (hanti _ _ (hw hub)).symm
  have : Finite (DedekindCut β) := Finite.of_injective _ Concept.extent_injective
  exact Nat.card_le_card_of_surjective _ hs

/-- The discrete order (antichain) on `Fin 2`. -/
@[instance_reducible] def antichain2 : PartialOrder (Fin 2) where
  le a b := a = b
  lt _ _ := False
  le_refl _ := rfl
  le_trans _ _ _ h1 h2 := h1.trans h2
  lt_iff_le_not_ge _ _ := ⟨False.elim, fun h => h.2 h.1.symm⟩
  le_antisymm _ _ h _ := h

/-- Non-vacuity check: the two-element antichain attains the bound (`|DM| = 4 = 2^2`). -/
theorem antichain2_attains : 2 ^ 2 ≤ Nat.card (@DedekindCut (Fin 2) antichain2.toPreorder) := by
  have h := @card_set_le_of_antichain_two (Fin 2) antichain2 _ (fun _ _ h => h)
    (fun w => ⟨if w = 0 then 1 else 0, by split_ifs <;> omega,
      fun a ha => by split_ifs <;> omega⟩)
  rwa [Nat.card_eq_fintype_card, Fintype.card_set, Fintype.card_fin] at h

theorem E_two_pos : 0 < E 2 := by
  have : Nonempty (Quot (@Iso 2)) := ⟨Quot.mk _ ⟨antichain2, antichain2_attains⟩⟩
  exact Nat.card_pos

theorem attaining_isEmpty {n : ℕ} (hn : 3 ≤ n) : IsEmpty (Attaining n) :=
  ⟨fun P => by
    have h := @card_cuts_lt (Fin n) P.1 _ (by simpa using hn)
    rw [Fintype.card_fin] at h
    exact absurd P.2 (not_le.2 h)⟩

/-- Even labelled posets: none on `n ≥ 3` points attains the bound. -/
theorem card_attaining_eq_zero {n : ℕ} (hn : 3 ≤ n) : Nat.card (Attaining n) = 0 := by
  have := attaining_isEmpty hn
  exact Nat.card_of_isEmpty

theorem E_eq_zero {n : ℕ} (hn : 3 ≤ n) : E n = 0 := by
  have := attaining_isEmpty hn
  exact Nat.card_of_isEmpty

theorem E_eventually_zero : ∀ᶠ n in atTop, E n = 0 :=
  eventually_atTop.2 ⟨3, fun _ hn => E_eq_zero hn⟩

/-- **Main theorem.** `E n = 0` for all `n ≥ 3`; hence `E` is not superpolynomial, neither in
the strong sense (eventually above every `n^k`) nor in the weak sense (not `O(n^k)` for any
`k`, i.e. `E n > C n^k` infinitely often for all `k, C`). -/
theorem not_superpolynomial :
    (∀ n, 3 ≤ n → E n = 0) ∧
    ¬ (∀ k : ℕ, ∀ᶠ n in atTop, n ^ k < E n) ∧
    ¬ (∀ k C : ℕ, ∃ᶠ n in atTop, C * n ^ k < E n) := by
  refine ⟨fun n hn => E_eq_zero hn, fun h => ?_, fun h => ?_⟩
  · obtain ⟨n, h1, h2⟩ := ((h 0).and E_eventually_zero).exists
    omega
  · obtain ⟨n, h1, h2⟩ := ((h 0 0).and_eventually E_eventually_zero).exists
    omega

end Conjecture2591
