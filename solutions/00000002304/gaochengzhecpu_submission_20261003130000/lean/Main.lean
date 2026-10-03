import Std
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Conjecture2304

structure GroupData (A : Type) where
  mul : A → A → A
  one : A
  inv : A → A
  assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
  one_mul : ∀ a, mul one a = a
  mul_one : ∀ a, mul a one = a
  inv_mul : ∀ a, mul (inv a) a = one
  mul_inv : ∀ a, mul a (inv a) = one

/-- All field axioms, including the inverse law and 0 ≠ 1. -/
structure FieldData (F : Type) where
  add : F → F → F
  zero : F
  neg : F → F
  mul : F → F → F
  one : F
  inv : F → F
  add_assoc : ∀ a b c, add (add a b) c = add a (add b c)
  add_comm : ∀ a b, add a b = add b a
  zero_add : ∀ a, add zero a = a
  neg_add : ∀ a, add (neg a) a = zero
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
  mul_comm : ∀ a b, mul a b = mul b a
  one_mul : ∀ a, mul one a = a
  mul_zero : ∀ a, mul a zero = zero
  distrib : ∀ a b c, mul a (add b c) = add (mul a b) (mul a c)
  inv_mul : ∀ a, a ≠ zero → mul (inv a) a = one
  zero_ne_one : zero ≠ one

/-- A vector space, with an abelian additive group and all scalar action laws. -/
structure VectorSpaceData {F : Type} (K : FieldData F) (V : Type) where
  additive : GroupData V
  add_comm : ∀ u v, additive.mul u v = additive.mul v u
  smul : F → V → V
  one_smul : ∀ v, smul K.one v = v
  mul_smul : ∀ a b v, smul (K.mul a b) v = smul a (smul b v)
  add_smul : ∀ a b v, smul (K.add a b) v =
    additive.mul (smul a v) (smul b v)
  smul_add : ∀ a u v, smul a (additive.mul u v) =
    additive.mul (smul a u) (smul a v)
  zero_smul : ∀ v, smul K.zero v = additive.one
  smul_zero : ∀ a, smul a additive.one = additive.one

structure LinearAction {G F V : Type} (H : GroupData G)
    (K : FieldData F) (W : VectorSpaceData K V) where
  act : G → V → V
  one_act : ∀ v, act H.one v = v
  mul_act : ∀ g h v, act (H.mul g h) v = act g (act h v)
  map_add : ∀ g u v, act g (W.additive.mul u v) =
    W.additive.mul (act g u) (act g v)
  map_smul : ∀ g a v, act g (W.smul a v) = W.smul a (act g v)

/-- A group action is faithful exactly when equality of its action maps implies equality in G. -/
def Faithful {G F V : Type} {H : GroupData G} {K : FieldData F}
    {W : VectorSpaceData K V} (ρ : LinearAction H K W) : Prop :=
  ∀ g h, (∀ v, ρ.act g v = ρ.act h v) → g = h

theorem action_inverse {G F V : Type} {H : GroupData G} {K : FieldData F}
    {W : VectorSpaceData K V} (ρ : LinearAction H K W) (g : G) (v : V) :
    ρ.act (H.inv g) (ρ.act g v) = v := by
  rw [← ρ.mul_act, H.inv_mul, ρ.one_act]

abbrev Bit := Fin 2
def add2 (x y : Bit) : Bit := ⟨(x.val + y.val) % 2, Nat.mod_lt _ (by decide)⟩
def mul2 (x y : Bit) : Bit := ⟨(x.val * y.val) % 2, Nat.mod_lt _ (by decide)⟩
def C2 : GroupData Bit where
  mul := add2
  one := 0
  inv := id
  assoc := by decide
  one_mul := by decide
  mul_one := by decide
  inv_mul := by decide
  mul_inv := by decide
def F2 : FieldData Bit where
  add := add2
  zero := 0
  neg := id
  mul := mul2
  one := 1
  inv := id
  add_assoc := by decide
  add_comm := by decide
  zero_add := by decide
  neg_add := by decide
  mul_assoc := by decide
  mul_comm := by decide
  one_mul := by decide
  mul_zero := by decide
  distrib := by decide
  inv_mul := by decide
  zero_ne_one := by decide
def V2 : VectorSpaceData F2 Bit where
  additive := C2
  add_comm := by decide
  smul := mul2
  one_smul := by decide
  mul_smul := by decide
  add_smul := by decide
  smul_add := by decide
  zero_smul := by decide
  smul_zero := by decide

theorem every_vector_is_scalar : ∀ v : Bit, V2.smul v 1 = v := by decide
theorem basis_vector_nonzero : (1 : Bit) ≠ V2.additive.one := by decide

def trivialAction : LinearAction C2 F2 V2 where
  act := fun _ v => v
  one_act := by decide
  mul_act := by decide
  map_add := by decide
  map_smul := by decide

theorem not_faithful : ¬Faithful trivialAction := by
  intro h
  have bad : (0 : Bit) = 1 := h 0 1 (fun _ => rfl)
  exact (by decide : (0 : Bit) ≠ 1) bad

/-- The conventional product on V ⋊ G: (v,g)(w,h)=(v+g·w,gh). -/
def semidirectMul (ρ : LinearAction C2 F2 V2) (x y : Bit × Bit) : Bit × Bit :=
  (V2.additive.mul x.1 (ρ.act x.2 y.1), C2.mul x.2 y.2)

instance finiteExists (n : Nat) (P : Fin n → Prop) [DecidablePred P] :
    Decidable (∃ x, P x) :=
  decidable_of_iff (¬∀ x, ¬P x) (by
    constructor
    · intro h
      obtain ⟨x, hx⟩ := Classical.not_forall.mp h
      exact ⟨x, Classical.byContradiction hx⟩
    · intro h hn
      obtain ⟨x, hx⟩ := h
      exact hn x hx)
instance pairForall (P : Bit × Bit → Prop) [DecidablePred P] :
    Decidable (∀ x, P x) :=
  decidable_of_iff (∀ a b, P (a, b)) (by
    constructor
    · intro h x
      exact h x.1 x.2
    · intro h a b
      exact h (a, b))
instance pairExists (P : Bit × Bit → Prop) [DecidablePred P] :
    Decidable (∃ x, P x) :=
  decidable_of_iff (∃ a b, P (a, b)) (by
    constructor
    · intro h
      obtain ⟨a, b, hab⟩ := h
      exact ⟨(a, b), hab⟩
    · intro h
      obtain ⟨⟨a, b⟩, hab⟩ := h
      exact ⟨a, b, hab⟩)

/-- The genuine semidirect product for the verified linear action, on the entire product carrier. -/
def GV : GroupData (Bit × Bit) where
  mul := semidirectMul trivialAction
  one := (0, 0)
  inv := id
  assoc := by decide
  one_mul := by decide
  mul_one := by decide
  inv_mul := by decide
  mul_inv := by decide

theorem semidirect_multiplication :
    GV.mul = semidirectMul trivialAction := rfl
theorem semidirect_identity : GV.one = (V2.additive.one, C2.one) := rfl

/-- Actual conjugacy, not a numerical surrogate for the number of classes. -/
def Conjugate {A : Type} (H : GroupData A) (x y : A) : Prop :=
  ∃ g, H.mul (H.mul g x) (H.inv g) = y
def Bijective {A B : Type} (f : A → B) : Prop :=
  (∀ a b, f a = f b → a = b) ∧ ∀ b, ∃ a, f a = b

/-- The conjugacy-class quotient has exactly n elements: an explicit bijection with Fin n. -/
def HasClassNumber {A : Type} (H : GroupData A) (n : Nat) : Prop :=
  ∃ s : Setoid A, (∀ x y, s.r x y ↔ Conjugate H x y) ∧
    ∃ f : Fin n → Quotient s, Bijective f

def equalitySetoid (A : Type) : Setoid A where
  r := Eq
  iseqv := ⟨Eq.refl, Eq.symm, Eq.trans⟩

theorem classes_from_equality {A : Type} (H : GroupData A) (n : Nat)
    (hconj : ∀ x y, Conjugate H x y ↔ x = y)
    (f : Fin n → A) (hf : Bijective f) : HasClassNumber H n := by
  refine ⟨equalitySetoid A, fun x y => (hconj x y).symm,
    fun i => Quotient.mk (equalitySetoid A) (f i), ?_⟩
  constructor
  · intro i j hij
    exact hf.1 i j (Quotient.exact hij)
  · intro q
    refine Quotient.inductionOn q ?_
    intro a
    obtain ⟨i, hi⟩ := hf.2 a
    exact ⟨i, congrArg (Quotient.mk (equalitySetoid A)) hi⟩

instance (x y : Bit) : Decidable (Conjugate C2 x y) :=
  inferInstanceAs (Decidable (∃ g : Bit, add2 (add2 g x) g = y))
instance (x y : Bit × Bit) : Decidable (Conjugate GV x y) :=
  inferInstanceAs (Decidable (∃ g : Bit × Bit, GV.mul (GV.mul g x) (GV.inv g) = y))

theorem conjugacy_C2 : ∀ x y : Bit, Conjugate C2 x y ↔ x = y := by decide
theorem conjugacy_GV : ∀ x y : Bit × Bit, Conjugate GV x y ↔ x = y := by decide

def pairCode (i : Fin 4) : Bit × Bit :=
  match i.val with
  | 0 => (0, 0) | 1 => (0, 1) | 2 => (1, 0) | _ => (1, 1)

theorem pairCode_bijective : Bijective pairCode := by
  unfold Bijective
  decide
theorem C2_class_number : HasClassNumber C2 2 :=
  classes_from_equality C2 2 conjugacy_C2 id
    ⟨fun _ _ h => h, fun x => ⟨x, rfl⟩⟩
theorem V2_class_number : HasClassNumber V2.additive 2 := C2_class_number
theorem GV_class_number : HasClassNumber GV 4 :=
  classes_from_equality GV 4 conjugacy_GV pairCode pairCode_bijective

/-- A necessary implication of the source's equality classification,
already restricted to the fixed genuine finite group, field, and vector space above. -/
def ClaimedEqualityNecessity : Prop :=
  ∀ (ρ : LinearAction C2 F2 V2) (H : GroupData (Bit × Bit)),
    H.mul = semidirectMul ρ → H.one = (V2.additive.one, C2.one) →
    ∀ kG kV kGV : Nat,
      HasClassNumber C2 kG → HasClassNumber V2.additive kV →
      HasClassNumber H kGV → kGV = kG * kV → Faithful ρ

theorem counterexample :
    HasClassNumber C2 2 ∧ HasClassNumber V2.additive 2 ∧
    HasClassNumber GV 4 ∧ 4 = 2 * 2 ∧ ¬Faithful trivialAction :=
  ⟨C2_class_number, V2_class_number, GV_class_number, rfl, not_faithful⟩

theorem conjecture2304_false : ¬ClaimedEqualityNecessity := by
  intro h
  exact not_faithful (h trivialAction GV semidirect_multiplication semidirect_identity
    2 2 4 C2_class_number V2_class_number GV_class_number rfl)

#print axioms GV_class_number
#print axioms counterexample
#print axioms conjecture2304_false

end Conjecture2304
