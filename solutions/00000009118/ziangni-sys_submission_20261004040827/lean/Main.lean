import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Card

namespace FiniteKakeya9118

/-- The actual two-dimensional vector space over the field with two elements. -/
abbrev Point := Fin 2 → ZMod 2

/-- An affine line has the standard parameterization a + t v. -/
def affinePoint (a v : Point) (t : ZMod 2) : Point := a + t • v

/-- The finite-field Kakeya condition: a whole affine line in each nonzero direction. -/
def IsKakeya (K : Finset Point) : Prop :=
  ∀ v : Point, v ≠ 0 → ∃ a : Point, ∀ t : ZMod 2, affinePoint a v t ∈ K

/-- Our set consists of all points except the origin. -/
def puncturedPlane : Finset Point := Finset.univ.erase 0

theorem scalar_field : Nonempty (Field (ZMod 2)) := ⟨inferInstance⟩

theorem field_card : Fintype.card (ZMod 2) = 2 := by decide

theorem ambient_card : Fintype.card Point = 4 := by decide

theorem puncturedPlane_card : puncturedPlane.card = 3 := by decide

/-- This checks the full direction/base-point/scalar quantification in the field. -/
theorem puncturedPlane_isKakeya : IsKakeya puncturedPlane := by
  unfold IsKakeya
  decide

/-- Nonzero directions really parameterize lines of q distinct points. -/
theorem affinePoint_injective :
    ∀ a v : Point, v ≠ 0 → Function.Injective (affinePoint a v) := by decide

/-- The conjectured q^n bound already fails for q = 2 and n = 2. -/
theorem conjecture_00000009118 :
    IsKakeya puncturedPlane ∧
    puncturedPlane.card < Fintype.card (ZMod 2) ^ (2 : ℕ) := by
  exact ⟨puncturedPlane_isKakeya, by decide⟩

theorem universal_bound_false :
    ¬ (∀ K : Finset Point, IsKakeya K →
      Fintype.card (ZMod 2) ^ (2 : ℕ) ≤ K.card) := by
  intro h
  exact (Nat.not_le_of_gt conjecture_00000009118.2)
    (h puncturedPlane puncturedPlane_isKakeya)

end FiniteKakeya9118

#print axioms FiniteKakeya9118.conjecture_00000009118
#print axioms FiniteKakeya9118.universal_bound_false
#print axioms FiniteKakeya9118.affinePoint_injective
