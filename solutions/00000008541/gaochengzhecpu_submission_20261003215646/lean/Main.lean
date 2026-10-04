import Std

namespace Conjecture8541
universe u
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- A lattice, with its order and the defining greatest/lower and least/upper
    bound properties. No distributive or bounded-lattice law is assumed. -/
structure Lattice (A : Type u) where
  le : A → A → Prop
  refl : ∀ x, le x x
  antisymm : ∀ x y, le x y → le y x → x=y
  trans : ∀ x y z, le x y → le y z → le x z
  meet : A → A → A
  join : A → A → A
  meet_left : ∀ x y, le (meet x y) x
  meet_right : ∀ x y, le (meet x y) y
  le_meet : ∀ x y z, le z x → le z y → le z (meet x y)
  join_left : ∀ x y, le x (join x y)
  join_right : ∀ x y, le y (join x y)
  join_le : ∀ x y z, le x z → le y z → le (join x y) z

theorem meet_of_le {A : Type u} (L : Lattice A) {a b : A} (h : L.le a b) :
    L.meet a b = a :=
  L.antisymm _ _ (L.meet_left a b) (L.le_meet a b a (L.refl a) h)
theorem meet_of_ge {A : Type u} (L : Lattice A) {a b : A} (h : L.le b a) :
    L.meet a b = b :=
  L.antisymm _ _ (L.meet_right a b) (L.le_meet a b b h (L.refl b))
theorem join_of_le {A : Type u} (L : Lattice A) {a b : A} (h : L.le a b) :
    L.join a b = b :=
  L.antisymm _ _ (L.join_le a b b h (L.refl b)) (L.join_right a b)
theorem join_of_ge {A : Type u} (L : Lattice A) {a b : A} (h : L.le b a) :
    L.join a b = a :=
  L.antisymm _ _ (L.join_le a b a (L.refl a) h) (L.join_left a b)
theorem meet_comm {A : Type u} (L : Lattice A) (a b : A) : L.meet a b = L.meet b a :=
  L.antisymm _ _
    (L.le_meet b a _ (L.meet_right a b) (L.meet_left a b))
    (L.le_meet a b _ (L.meet_right b a) (L.meet_left b a))
theorem join_comm {A : Type u} (L : Lattice A) (a b : A) : L.join a b = L.join b a :=
  L.antisymm _ _
    (L.join_le a b _ (L.join_right b a) (L.join_left b a))
    (L.join_le b a _ (L.join_right a b) (L.join_left a b))

abbrev E := Fin 4
def below (x y : E) : Prop := x=0 ∨ y=3 ∨ x=y
instance (x y : E) : Decidable (below x y) := by unfold below; infer_instance
def meet (x y : E) : E := if x=3 then y else if y=3 then x else if x=y then x else 0
def join (x y : E) : E := if x=0 then y else if y=0 then x else if x=y then x else 3
def freeTwo : Lattice E where
  le := below
  refl := by decide
  antisymm := by decide
  trans := by decide
  meet := meet
  join := join
  meet_left := by decide
  meet_right := by decide
  le_meet := by decide
  join_left := by decide
  join_right := by decide
  join_le := by decide

def image {A : Type u} (L : Lattice A) (a b : A) (x : E) : A :=
  match x.val with
  | 0 => L.meet a b | 1 => a | 2 => b | _ => L.join a b
def Hom {A : Type u} (L : Lattice A) (h : E → A) : Prop :=
  (∀ x y, h (meet x y) = L.meet (h x) (h y)) ∧
  (∀ x y, h (join x y) = L.join (h x) (h y))

theorem image_hom {A : Type u} (L : Lattice A) (a b : A) : Hom L (image L a b) := by
  have all : ∀ x : E, x=0 ∨ x=1 ∨ x=2 ∨ x=3 := by decide
  have hmj := L.trans _ _ _ (L.meet_left a b) (L.join_left a b)
  have hmA := L.meet_left a b
  have hmB := L.meet_right a b
  have hAj := L.join_left a b
  have hBj := L.join_right a b
  constructor <;> intro x y <;>
    rcases all x with rfl | rfl | rfl | rfl <;>
    rcases all y with rfl | rfl | rfl | rfl <;>
    simp only [image, meet, join, Fin.isValue, ↓reduceIte] <;>
    first
    | rfl
    | exact (meet_of_le L (L.refl _)).symm
    | exact (join_of_le L (L.refl _)).symm
    | exact (meet_of_le L hmA).symm
    | exact (meet_of_le L hmB).symm
    | exact (meet_of_le L hAj).symm
    | exact (meet_of_le L hBj).symm
    | exact (meet_of_le L hmj).symm
    | exact (meet_of_ge L hmA).symm
    | exact (meet_of_ge L hmB).symm
    | exact (meet_of_ge L hAj).symm
    | exact (meet_of_ge L hBj).symm
    | exact (meet_of_ge L hmj).symm
    | exact (join_of_le L hmA).symm
    | exact (join_of_le L hmB).symm
    | exact (join_of_le L hAj).symm
    | exact (join_of_le L hBj).symm
    | exact (join_of_le L hmj).symm
    | exact (join_of_ge L hmA).symm
    | exact (join_of_ge L hmB).symm
    | exact (join_of_ge L hAj).symm
    | exact (join_of_ge L hBj).symm
    | exact (join_of_ge L hmj).symm
    | exact meet_comm L a b
    | exact join_comm L a b

/-- The full universal property, for every lattice and every two chosen
    elements: existence and uniqueness of the extending homomorphism. -/
theorem free_on_two_generators {A : Type u} (L : Lattice A) (a b : A) :
    ∃ h : E → A, Hom L h ∧ h 1=a ∧ h 2=b ∧
      ∀ g : E → A, Hom L g → g 1=a → g 2=b → g=h := by
  refine ⟨image L a b, image_hom L a b, rfl, rfl, ?_⟩
  intro g hg ha hb
  funext x
  have all : ∀ x : E, x=0 ∨ x=1 ∨ x=2 ∨ x=3 := by decide
  rcases all x with rfl | rfl | rfl | rfl
  · have h := hg.1 1 2
    simpa only [meet, Fin.isValue, ↓reduceIte, ha, hb, image] using h
  · exact ha
  · exact hb
  · have h := hg.2 1 2
    simpa only [join, Fin.isValue, ↓reduceIte, ha, hb, image] using h

/-- Every conceivable choice of length balls is covered, even if no length
    convention is fixed in the original statement. -/
noncomputable def count (S : E → Prop) : Nat := by
  classical
  exact ((List.finRange 4).filter (fun x => decide (S x))).length
theorem every_subset_has_at_most_four (S : E → Prop) : count S ≤ 4 := by
  classical
  exact List.length_filter_le _ (List.finRange 4)
def UnboundedGrowth (b : Nat → Nat) : Prop := ∀ M : Nat, ∃ l : Nat, M < b l
theorem conjecture8541_counterexample (balls : Nat → E → Prop) :
    (∀ l, count (balls l) ≤ 4) ∧ ¬ UnboundedGrowth (fun l => count (balls l)) := by
  refine ⟨fun l => every_subset_has_at_most_four (balls l), ?_⟩
  intro h
  obtain ⟨l, hl⟩ := h 4
  change 4 < count (balls l) at hl
  have hb := every_subset_has_at_most_four (balls l)
  omega

end Conjecture8541
#print axioms Conjecture8541.free_on_two_generators
#print axioms Conjecture8541.conjecture8541_counterexample
