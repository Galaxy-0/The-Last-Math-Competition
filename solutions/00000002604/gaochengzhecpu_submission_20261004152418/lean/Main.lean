import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Order.Cover
import Mathlib.Order.Fin.Basic
import Mathlib.Order.Hom.Basic
import Mathlib.Order.Lattice
import Mathlib.Tactic.IntervalCases

/-! Two finite distributive lattices with eight elements have the same layer-count vector
`(1, 2, 2, 2, 1)`, counted from the bottom or from the top, and are not isomorphic. -/
namespace Conjecture2604

/-! ### Rank functions and layer counts -/

section Layers

variable {α : Type} [PartialOrder α] [BoundedOrder α]

/-- A rank function: zero at the bottom, increasing by one along every covering relation. -/
def IsRankFunction (g : α → ℕ) : Prop :=
  g ⊥ = 0 ∧ ∀ a b : α, a ⋖ b → g b = g a + 1

/-- A corank function: zero at the top, increasing by one going down every covering relation.
Its layer `1` is the set of coatoms. -/
def IsCorankFunction (h : α → ℕ) : Prop :=
  h ⊤ = 0 ∧ ∀ a b : α, a ⋖ b → h a = h b + 1

end Layers

/-- The number of elements in layer `k` of a function to `ℕ`. -/
def layer {α : Type} [Fintype α] (g : α → ℕ) (k : ℕ) : ℕ :=
  (Finset.univ.filter (fun a => g a = k)).card

theorem layer_eq_zero {α : Type} [Fintype α] (g : α → ℕ) (hg : ∀ a, g a < 5) (k : ℕ)
    (hk : 5 ≤ k) : layer g k = 0 := by
  unfold layer
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro a _ h
  have h5 := hg a
  omega

/-! ### Decidability of the componentwise order on a product of two finite chains -/

instance decLE {m n : ℕ} : DecidableRel (α := Fin m × Fin n) (· ≤ ·) := fun a b =>
  inferInstanceAs (Decidable (a.1 ≤ b.1 ∧ a.2 ≤ b.2))

instance decLT {m n : ℕ} : DecidableRel (α := Fin m × Fin n) (· < ·) := fun a b =>
  decidable_of_iff (a ≤ b ∧ ¬ b ≤ a) lt_iff_le_not_le.symm

/-! ### The first lattice: the product of a four-chain and a two-chain -/

/-- `L1` is the product of the chains `0 < 1 < 2 < 3` and `0 < 1`. It is the lattice of order
ideals of the poset consisting of a three-chain and an isolated point. -/
abbrev L1 := Fin 4 × Fin 2

def rank1 (x : L1) : ℕ := x.1.val + x.2.val

def corank1 (x : L1) : ℕ := 4 - (x.1.val + x.2.val)

theorem rank1_cover : ∀ a b : L1, a < b → (∀ c : L1, a < c → ¬ c < b) →
    rank1 b = rank1 a + 1 := by decide

theorem corank1_cover : ∀ a b : L1, a < b → (∀ c : L1, a < c → ¬ c < b) →
    corank1 a = corank1 b + 1 := by decide

theorem isRankFunction_rank1 : IsRankFunction rank1 :=
  ⟨rfl, fun a b hab => rank1_cover a b hab.lt fun _ h1 h2 => hab.2 h1 h2⟩

theorem isCorankFunction_corank1 : IsCorankFunction corank1 :=
  ⟨rfl, fun a b hab => corank1_cover a b hab.lt fun _ h1 h2 => hab.2 h1 h2⟩

/-! ### The second lattice: a sublattice of the product of two three-chains -/

/-- The pairs `(i, j)` in `{0,1,2} × {0,1,2}` other than `(2, 0)`. -/
def InL2 (p : Fin 3 × Fin 3) : Prop := p.1 = 2 → p.2 ≠ 0

instance : DecidablePred InL2 := fun p => by unfold InL2; infer_instance

theorem inL2_sup : ∀ p q : Fin 3 × Fin 3, InL2 p → InL2 q → InL2 (p ⊔ q) := by decide

theorem inL2_inf : ∀ p q : Fin 3 × Fin 3, InL2 p → InL2 q → InL2 (p ⊓ q) := by decide

/-- `L2` is closed under the componentwise maximum and minimum, so it is a sublattice of the
distributive lattice `Fin 3 × Fin 3`. It is the lattice of order ideals of the four-element
poset `N` with relations `a < c`, `b < c`, `b < d`. -/
abbrev L2 := {p : Fin 3 × Fin 3 // InL2 p}

instance : DistribLattice L2 where
  __ := Subtype.lattice (fun p q hp hq => inL2_sup p q hp hq) (fun p q hp hq => inL2_inf p q hp hq)
  le_sup_inf x y z := le_sup_inf (x := x.1) (y := y.1) (z := z.1)

instance : BoundedOrder L2 where
  bot := ⟨(0, 0), by decide⟩
  bot_le x := by
    change ((0, 0) : Fin 3 × Fin 3) ≤ x.1
    exact ⟨Fin.zero_le _, Fin.zero_le _⟩
  top := ⟨(2, 2), by decide⟩
  le_top x := by
    change x.1 ≤ ((2, 2) : Fin 3 × Fin 3)
    exact ⟨Fin.le_last _, Fin.le_last _⟩

instance : DecidableRel (α := L2) (· ≤ ·) := fun a b =>
  inferInstanceAs (Decidable (a.1 ≤ b.1))

instance : DecidableRel (α := L2) (· < ·) := fun a b =>
  inferInstanceAs (Decidable (a.1 < b.1))

def rank2 (x : L2) : ℕ := x.1.1.val + x.1.2.val

def corank2 (x : L2) : ℕ := 4 - (x.1.1.val + x.1.2.val)

theorem rank2_cover : ∀ a b : L2, a < b → (∀ c : L2, a < c → ¬ c < b) →
    rank2 b = rank2 a + 1 := by decide

theorem corank2_cover : ∀ a b : L2, a < b → (∀ c : L2, a < c → ¬ c < b) →
    corank2 a = corank2 b + 1 := by decide

theorem isRankFunction_rank2 : IsRankFunction rank2 :=
  ⟨rfl, fun a b hab => rank2_cover a b hab.lt fun _ h1 h2 => hab.2 h1 h2⟩

theorem isCorankFunction_corank2 : IsCorankFunction corank2 :=
  ⟨rfl, fun a b hab => corank2_cover a b hab.lt fun _ h1 h2 => hab.2 h1 h2⟩

/-! ### Both lattices have eight elements and layer-count vector `(1, 2, 2, 2, 1)` -/

theorem card_L1 : Fintype.card L1 = 8 := by decide

theorem card_L2 : Fintype.card L2 = 8 := by decide

theorem layers_rank1 : (List.range 5).map (layer rank1) = [1, 2, 2, 2, 1] := by decide

theorem layers_rank2 : (List.range 5).map (layer rank2) = [1, 2, 2, 2, 1] := by decide

theorem layers_corank1 : (List.range 5).map (layer corank1) = [1, 2, 2, 2, 1] := by decide

theorem layers_corank2 : (List.range 5).map (layer corank2) = [1, 2, 2, 2, 1] := by decide

theorem rank1_lt : ∀ a : L1, rank1 a < 5 := by decide

theorem rank2_lt : ∀ a : L2, rank2 a < 5 := by decide

theorem corank1_lt : ∀ a : L1, corank1 a < 5 := by decide

theorem corank2_lt : ∀ a : L2, corank2 a < 5 := by decide

theorem layer_rank_eq (k : ℕ) : layer rank1 k = layer rank2 k := by
  by_cases hk : k < 5
  · interval_cases k <;> decide
  · rw [layer_eq_zero rank1 rank1_lt k (by omega), layer_eq_zero rank2 rank2_lt k (by omega)]

theorem layer_corank_eq (k : ℕ) : layer corank1 k = layer corank2 k := by
  by_cases hk : k < 5
  · interval_cases k <;> decide
  · rw [layer_eq_zero corank1 corank1_lt k (by omega),
      layer_eq_zero corank2 corank2_lt k (by omega)]

/-! ### The lattices are not isomorphic -/

/-- In `L1`, an element with two incomparable elements below it has second coordinate `1`. -/
theorem L1_two_below : ∀ x a b : L1, a < x → b < x → ¬ a ≤ b → ¬ b ≤ a → x.2 = 1 := by decide

/-- In `L1`, an element with two incomparable elements above it has second coordinate `0`. -/
theorem L1_two_above : ∀ x c d : L1, x < c → x < d → ¬ c ≤ d → ¬ d ≤ c → x.2 = 0 := by decide

def X : L2 := ⟨(1, 1), by decide⟩
def A : L2 := ⟨(1, 0), by decide⟩
def B : L2 := ⟨(0, 1), by decide⟩
def C : L2 := ⟨(2, 1), by decide⟩
def D : L2 := ⟨(1, 2), by decide⟩

theorem L2_branch : A < X ∧ B < X ∧ ¬ A ≤ B ∧ ¬ B ≤ A ∧ X < C ∧ X < D ∧ ¬ C ≤ D ∧ ¬ D ≤ C := by
  decide

/-- No order isomorphism exists: the element `(1, 1)` of `L2` has two incomparable elements
below it and two incomparable elements above it, and no element of `L1` does. -/
theorem not_isomorphic : IsEmpty (L1 ≃o L2) := by
  refine ⟨fun e => ?_⟩
  obtain ⟨hA, hB, hAB, hBA, hC, hD, hCD, hDC⟩ := L2_branch
  have h1 : (e.symm X).2 = 1 :=
    L1_two_below (e.symm X) (e.symm A) (e.symm B)
      (e.symm.lt_iff_lt.mpr hA) (e.symm.lt_iff_lt.mpr hB)
      (fun h => hAB (e.symm.le_iff_le.mp h)) (fun h => hBA (e.symm.le_iff_le.mp h))
  have h0 : (e.symm X).2 = 0 :=
    L1_two_above (e.symm X) (e.symm C) (e.symm D)
      (e.symm.lt_iff_lt.mpr hC) (e.symm.lt_iff_lt.mpr hD)
      (fun h => hCD (e.symm.le_iff_le.mp h)) (fun h => hDC (e.symm.le_iff_le.mp h))
  rw [h1] at h0
  exact absurd h0 (by decide)

/-! ### The conjectured rigidity and its negation -/

/-- Rigidity for layers counted from the bottom: finite distributive lattices whose rank
functions have equal layer counts are isomorphic. -/
def ClaimedRankRigidity : Prop :=
  ∀ (α β : Type) [DistribLattice α] [BoundedOrder α] [Fintype α]
    [DistribLattice β] [BoundedOrder β] [Fintype β] (g : α → ℕ) (h : β → ℕ),
    IsRankFunction g → IsRankFunction h → (∀ k, layer g k = layer h k) → Nonempty (α ≃o β)

/-- Rigidity for layers counted from the top (the coatom layer is layer `1`). -/
def ClaimedCoatomLayerRigidity : Prop :=
  ∀ (α β : Type) [DistribLattice α] [BoundedOrder α] [Fintype α]
    [DistribLattice β] [BoundedOrder β] [Fintype β] (g : α → ℕ) (h : β → ℕ),
    IsCorankFunction g → IsCorankFunction h → (∀ k, layer g k = layer h k) →
    Nonempty (α ≃o β)

theorem rank_rigidity_false : ¬ ClaimedRankRigidity := fun hR =>
  not_isomorphic.elim' (hR L1 L2 rank1 rank2 isRankFunction_rank1 isRankFunction_rank2
    layer_rank_eq).some

theorem conjecture_false : ¬ ClaimedCoatomLayerRigidity := fun hR =>
  not_isomorphic.elim' (hR L1 L2 corank1 corank2 isCorankFunction_corank1
    isCorankFunction_corank2 layer_corank_eq).some

#print axioms isRankFunction_rank1
#print axioms isRankFunction_rank2
#print axioms isCorankFunction_corank1
#print axioms isCorankFunction_corank2
#print axioms layers_rank1
#print axioms layers_rank2
#print axioms layer_rank_eq
#print axioms layer_corank_eq
#print axioms not_isomorphic
#print axioms rank_rigidity_false
#print axioms conjecture_false

end Conjecture2604
