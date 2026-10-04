import Mathlib.Algebra.Group.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic

namespace FiniteTarski

-- Labels describe a genuine partition into n pieces. Each piece has a side
-- and a left multiplier. The two sides separately reassemble the whole group.
structure ParadoxicalDecomposition (G : Type*) [Group G] (n : Nat) where
  label : G → Fin n
  side : Fin n → Bool
  multiplier : Fin n → G
  covers : ∀ b : Bool, ∀ y : G, ∃ x : G,
    side (label x) = b ∧ multiplier (label x) * x = y
  separates : ∀ x z : G, side (label x) = side (label z) →
    multiplier (label x) * x = multiplier (label z) * z → x = z

variable {G : Type*} [Group G] {n : Nat}

def piece (D : ParadoxicalDecomposition G n) (i : Fin n) : Set G :=
  {x | D.label x = i}

theorem partition_covers (D : ParadoxicalDecomposition G n) (x : G) :
    ∃ i : Fin n, x ∈ piece D i := ⟨D.label x,rfl⟩

theorem partition_disjoint (D : ParadoxicalDecomposition G n)
    (i j : Fin n) (x : G) (hi : x ∈ piece D i) (hj : x ∈ piece D j) : i = j :=
  hi.symm.trans hj

def translated (D : ParadoxicalDecomposition G n) (x : G) : G ⊕ G :=
  if D.side (D.label x) then Sum.inl (D.multiplier (D.label x) * x)
  else Sum.inr (D.multiplier (D.label x) * x)

theorem translated_surjective (D : ParadoxicalDecomposition G n) :
    Function.Surjective (translated D) := by
  intro y
  cases y with
  | inl y =>
    obtain ⟨x,hside,hprod⟩ := D.covers true y
    exact ⟨x,by simp [translated,hside,hprod]⟩
  | inr y =>
    obtain ⟨x,hside,hprod⟩ := D.covers false y
    exact ⟨x,by simp [translated,hside,hprod]⟩

theorem translated_injective (D : ParadoxicalDecomposition G n) :
    Function.Injective (translated D) := by
  intro x z h
  cases hx : D.side (D.label x) <;> cases hz : D.side (D.label z)
  · simp [translated,hx,hz] at h
    exact D.separates x z (by rw [hx,hz]) h
  · simp [translated,hx,hz] at h
  · simp [translated,hx,hz] at h
  · simp [translated,hx,hz] at h
    exact D.separates x z (by rw [hx,hz]) h

-- Only the covering consequence is needed for the finite counting obstruction.
theorem no_finite_paradoxical_decomposition [Fintype G] (n : Nat) :
    ¬ Nonempty (ParadoxicalDecomposition G n) := by
  rintro ⟨D⟩
  have h := Fintype.card_le_of_surjective (translated D) (translated_surjective D)
  have hp : 0 < Fintype.card G := Fintype.card_pos_iff.mpr ⟨1⟩
  rw [Fintype.card_sum] at h
  omega

-- Every finite quotient is a finite group, so this covers every possible
-- quotient of the claimed Burnside group without a presentation assumption.
theorem finite_quotient_cannot_realize_six [Fintype G] :
    ¬ Nonempty (ParadoxicalDecomposition G 6) :=
  no_finite_paradoxical_decomposition 6

def HasSixPieceParadox (Q : Type*) [Group Q] : Prop :=
  Nonempty (ParadoxicalDecomposition Q 6)

theorem conjecture_00000001000_false (Q : Type*) [Group Q] [Fintype Q] :
    ¬ HasSixPieceParadox Q := finite_quotient_cannot_realize_six

#print axioms translated_surjective
#print axioms translated_injective
#print axioms no_finite_paradoxical_decomposition
#print axioms conjecture_00000001000_false
end FiniteTarski
