import Mathlib

/-!
# Conjecture 00000003524: two stationary subsets of omega_1 can be disjoint

English statement: "Definition: Subsets of omega_1: the combinatorics of uncountable ordinals.
Conjecture: Club sets and stationary sets: the intersection of stationary sets is stationary,
with the reflection of stationarity bounded below closure."

We refute the first conjunct, "the intersection of stationary sets is stationary", for subsets
of `ω₁` (Mathlib's `(ω₁).ToType`, whose elements are the countable ordinals), with Mathlib's own
`IsClub` and `IsStationary` from `Mathlib/SetTheory/Cardinal/Cofinality/Club.lean`.

The argument is the Ulam matrix. For each `a` fix `f a : α → ℕ`, injective on `Iio a`. For `n : ℕ`
and `b : α` put `A n b = {a | b < a ∧ f a b = n}`. For fixed `b`, the sets `A n b` (`n : ℕ`)
cover `Ioi b`, which is stationary, so some `A (N b) b` is stationary. The map `N : α → ℕ`
is not injective because `α` is uncountable, so `N b = N b'` for some `b ≠ b'`. Then
`A (N b) b` and `A (N b') b'` are disjoint, because each `f a` is injective on `Iio a`.
-/

open Cardinal Set

namespace C3524

/-! ### Mathlib's definitions, unfolded -/

/-- Mathlib's `IsClub` in a linear order, unfolded: the set contains the least upper bound of each
of its nonempty subsets that has one (closed), and it is cofinal (unbounded). -/
theorem isClub_iff_closed_unbounded {α : Type*} [LinearOrder α] (s : Set α) :
    IsClub s ↔ (∀ d ⊆ s, d.Nonempty → ∀ a, IsLUB d a → a ∈ s) ∧ (∀ x, ∃ y ∈ s, x ≤ y) := by
  rw [isClub_iff]
  exact ⟨fun ⟨h1, h2⟩ => ⟨fun d hd hne a ha => h1 hd hne (.of_linearOrder _) ha, h2⟩,
    fun ⟨h1, h2⟩ => ⟨fun d hd hne _ a ha => h1 d hd hne a ha, h2⟩⟩

/-- Mathlib's `IsStationary`, unfolded: the set meets every club set. -/
theorem isStationary_iff_meets_every_club {α : Type*} [LinearOrder α] (s : Set α) :
    IsStationary s ↔ ∀ t : Set α, IsClub t → (s ∩ t).Nonempty :=
  ⟨fun h _ ht => h ht, fun h _ ht => h _ ht⟩

/-! ### The Ulam matrix in a general well-order -/

section General

variable {α : Type*} [LinearOrder α]

/-- In an uncountable linear order whose initial segments are countable, every final segment
`Ioi b` is stationary (its complement `Iic b` is bounded). -/
theorem isStationary_Ioi [Uncountable α] (hIio : ∀ a : α, (Iio a).Countable) (b : α) :
    IsStationary (Ioi b) := by
  apply IsStationary.of_not_isCofinal_compl
  intro h
  have hsub : (univ : Set α) ⊆ insert b (Iio b) := by
    intro x _
    obtain ⟨y, hy, hxy⟩ := h x
    have hyb : y ≤ b := by simpa using hy
    rcases (hxy.trans hyb).lt_or_eq with h' | h'
    · exact Or.inr h'
    · exact Or.inl h'
  have hc : (univ : Set α).Countable := ((hIio b).insert b).mono hsub
  exact not_countable (countable_univ_iff.1 hc)

variable [WellFoundedLT α]

/-- Ulam: an uncountable well-order with countable initial segments and cofinality `≠ ℵ₀`
contains two disjoint stationary sets. -/
theorem exists_disjoint_stationary [Uncountable α] (hcof : Order.cof α ≠ ℵ₀)
    (hIio : ∀ a : α, (Iio a).Countable) :
    ∃ S T : Set α, IsStationary S ∧ IsStationary T ∧ Disjoint S T := by
  choose f hf using fun a : α => Set.countable_iff_exists_injOn.1 (hIio a)
  -- the Ulam matrix
  let A : ℕ → α → Set α := fun n b => {a | b < a ∧ f a b = n}
  have hcover : ∀ b, (⋃ n, A n b) = Ioi b := by
    intro b
    ext a
    simp [A]
  have hrow : ∀ b, ∃ n, IsStationary (A n b) := by
    intro b
    have h := isStationary_Ioi hIio b
    rw [← hcover b] at h
    exact (isStationary_iUnion_iff_of_countable hcof).1 h
  choose N hN using hrow
  have hNinj : ¬ Function.Injective N := fun h => not_countable h.countable
  simp only [Function.Injective, not_forall] at hNinj
  obtain ⟨b, b', hbb', hne⟩ := hNinj
  refine ⟨A (N b) b, A (N b') b', hN b, hN b', ?_⟩
  rw [Set.disjoint_left]
  rintro a ⟨hba, hfa⟩ ⟨hb'a, hfa'⟩
  exact hne (hf a hba hb'a (hfa.trans (hbb'.trans hfa'.symm)))

end General

/-! ### The case of omega_1 -/

open Ordinal

universe u

theorem mk_omega_one_toType : #(ω₁).ToType = ℵ₁ := by
  rw [mk_toType, card_omega]

instance uncountable_omega_one_toType : Uncountable (ω₁).ToType :=
  aleph0_lt_mk_iff.1 (by rw [mk_omega_one_toType]; exact aleph0_lt_aleph_one)

theorem cof_omega_one_toType : Order.cof (ω₁).ToType = ℵ₁ := by
  rw [Ordinal.cof_toType, cof_omega_one]

/-- Every proper initial segment of `ω₁` is countable. -/
theorem countable_Iio_omega_one (a : (ω₁).ToType) : (Iio a).Countable := by
  rw [← le_aleph0_iff_set_countable, ← lt_aleph_one_iff, ← mk_omega_one_toType]
  exact mk_Iio_lt a (by rw [mk_omega_one_toType, ord_aleph, type_toType])

/-- `ω₁` contains two disjoint stationary sets. -/
theorem exists_disjoint_stationary_omega_one :
    ∃ S T : Set (ω₁).ToType, IsStationary S ∧ IsStationary T ∧ Disjoint S T :=
  exists_disjoint_stationary (by rw [cof_omega_one_toType]; exact aleph0_lt_aleph_one.ne')
    countable_Iio_omega_one

/-- The literal first conjunct: the intersection of two stationary subsets of `ω₁` is
stationary. -/
def StationaryInterClaim : Prop :=
  ∀ S T : Set (ω₁ : Ordinal.{u}).ToType, IsStationary S → IsStationary T → IsStationary (S ∩ T)

/-- The first conjunct is false: there are stationary `S, T ⊆ ω₁` with `S ∩ T = ∅`, which is not
stationary. -/
theorem stationaryInterClaim_false : ¬ StationaryInterClaim.{u} := by
  intro h
  obtain ⟨S, T, hS, hT, hST⟩ := exists_disjoint_stationary_omega_one
  have h2 := h S T hS hT
  rw [Set.disjoint_iff_inter_eq_empty.1 hST] at h2
  exact not_isStationary_empty h2

/-- Family form: it is false that the intersection of every nonempty family of stationary subsets
of `ω₁` is stationary. -/
theorem sInter_claim_false :
    ¬ ∀ F : Set (Set (ω₁ : Ordinal.{u}).ToType), F.Nonempty → (∀ s ∈ F, IsStationary s) →
      IsStationary (⋂₀ F) := by
  intro h
  obtain ⟨S, T, hS, hT, hST⟩ := exists_disjoint_stationary_omega_one.{u}
  have h2 := h {S, T} (insert_nonempty S {T}) (by simp [hS, hT])
  rw [sInter_pair, Set.disjoint_iff_inter_eq_empty.1 hST] at h2
  exact not_isStationary_empty h2

/-- The intersection of all stationary subsets of `ω₁` is not stationary. -/
theorem not_isStationary_sInter_all :
    ¬ IsStationary (⋂₀ {s : Set (ω₁ : Ordinal.{u}).ToType | IsStationary s}) := by
  intro h
  obtain ⟨S, T, hS, hT, hST⟩ := exists_disjoint_stationary_omega_one.{u}
  have hsub : ⋂₀ {s : Set (ω₁ : Ordinal.{u}).ToType | IsStationary s} ⊆ S ∩ T :=
    subset_inter (sInter_subset_of_mem hS) (sInter_subset_of_mem hT)
  rw [Set.disjoint_iff_inter_eq_empty.1 hST, subset_empty_iff] at hsub
  rw [hsub] at h
  exact not_isStationary_empty h

/-- **Main theorem.** The conjecture is the conjunction (the Chinese text joins the clauses with
"and") of "the intersection of stationary sets is stationary" and a second clause, "the reflection
of stationarity bounded below closure", which states no definite proposition. Whatever
proposition `Q` the second clause is read as, the conjunction is false. -/
theorem conjecture3524_false (Q : Prop) : ¬ (StationaryInterClaim.{u} ∧ Q) :=
  fun h => stationaryInterClaim_false h.1

/-! ### Remark: the true variant (not the conjecture) -/

/-- For contrast, and not part of the refutation: a stationary set meets each club set of `ω₁`
in a stationary set. The conjecture's text says "stationary sets", not "a stationary set and a
club set". -/
theorem isStationary_inter_isClub {S C : Set (ω₁ : Ordinal.{u}).ToType} (hS : IsStationary S)
    (hC : IsClub C) :
    IsStationary (S ∩ C) := by
  intro t ht
  have hcof : Order.cof (ω₁ : Ordinal.{u}).ToType ≠ ℵ₀ := by
    rw [cof_omega_one_toType]; exact aleph0_lt_aleph_one.ne'
  obtain ⟨x, hxS, hxC, hxt⟩ := hS (hC.inter hcof ht)
  exact ⟨x, ⟨hxS, hxC⟩, hxt⟩

end C3524
