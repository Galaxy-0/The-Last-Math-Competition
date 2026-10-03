import Std

/-! The cube B_3 = C_2 x C_2 x C_2 has two distinct maximum antichains.
Elements and finite subsets are encoded by binary masks, so every
antichain check and the sharp upper bound is a complete finite check. -/
namespace Conjecture8544
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

abbrev Element := Fin 8
abbrev Subset := Fin 256

def bit (x : Element) (i : Fin 3) : Fin 2 :=
  ⟨(x.val / 2^i.val) % 2, Nat.mod_lt _ (by decide)⟩

def cube (x : Element) : Fin 2 × Fin 2 × Fin 2 := (bit x 0, bit x 1, bit x 2)

def unCube (a b c : Fin 2) : Element :=
  ⟨(a.val + 2*b.val + 4*c.val) % 8, Nat.mod_lt _ (by decide)⟩

theorem cube_left_inverse :
    ∀ x : Element, unCube (cube x).1 (cube x).2.1 (cube x).2.2 = x := by decide

theorem cube_right_inverse :
    ∀ a b c : Fin 2, cube (unCube a b c) = (a,b,c) := by decide

/-- Exactly the coordinatewise product order on three two-element chains. -/
def Below (x y : Element) : Prop :=
  (cube x).1 ≤ (cube y).1 ∧
  (cube x).2.1 ≤ (cube y).2.1 ∧ (cube x).2.2 ≤ (cube y).2.2

instance (x y : Element) : Decidable (Below x y) := by unfold Below; infer_instance

theorem factors_are_total_chains : ∀ x y : Fin 2, x ≤ y ∨ y ≤ x := by decide

theorem product_is_partial_order :
    (∀ x : Element, Below x x) ∧
    (∀ x y : Element, Below x y → Below y x → x = y) ∧
    (∀ x y z : Element, Below x y → Below y z → Below x z) := by decide

/-- Standard bit-mask representation of subsets of an eight-element set. -/
def member (s : Subset) (x : Element) : Bool := (s.val / 2^x.val) % 2 == 1

/-- Encode any eight Boolean membership decisions; this makes completeness
    of the subset enumeration explicit, rather than an external assumption. -/
def encodeBits (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) : Subset :=
  ⟨((if b0 then 1 else 0) + (if b1 then 2 else 0) +
     (if b2 then 4 else 0) + (if b3 then 8 else 0) +
     (if b4 then 16 else 0) + (if b5 then 32 else 0) +
     (if b6 then 64 else 0) + (if b7 then 128 else 0)) % 256,
     Nat.mod_lt _ (by decide)⟩

def table (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) (x : Element) : Bool :=
  match x.val with
  | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3
  | 4 => b4 | 5 => b5 | 6 => b6 | _ => b7

theorem encodeBits_correct :
    ∀ b0 b1 b2 b3 b4 b5 b6 b7 : Bool, ∀ x : Element,
      member (encodeBits b0 b1 b2 b3 b4 b5 b6 b7) x = table b0 b1 b2 b3 b4 b5 b6 b7 x := by
  decide

def encode (p : Element → Bool) : Subset :=
  encodeBits (p 0) (p 1) (p 2) (p 3) (p 4) (p 5) (p 6) (p 7)

theorem every_subset_encoded (p : Element → Bool) : member (encode p) = p := by
  funext x
  unfold encode
  rw [encodeBits_correct]
  have h : ∀ x : Element, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5 ∨ x = 6 ∨ x = 7 := by decide
  rcases h x with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

def cardinality (s : Subset) : Nat := ((List.finRange 8).filter (member s)).length

def Antichain (s : Subset) : Prop :=
  ∀ x y : Element, member s x = true → member s y = true → Below x y → x = y

instance (s : Subset) : Decidable (Antichain s) := by unfold Antichain; infer_instance

def MaximumAntichain (s : Subset) : Prop :=
  Antichain s ∧ ∀ a : Subset, Antichain a → cardinality a ≤ cardinality s

def UniqueMaximumAntichain : Prop :=
  ∀ a b : Subset, MaximumAntichain a → MaximumAntichain b → a = b

/-- Rank one: {001,010,100}; mask 2+4+16=22. -/
def rankOne : Subset := 22
/-- Rank two: {011,101,110}; mask 8+32+64=104. -/
def rankTwo : Subset := 104

theorem rankOne_members :
    ∀ x : Element, member rankOne x = true ↔ (x = 1 ∨ x = 2 ∨ x = 4) := by decide

theorem rankTwo_members :
    ∀ x : Element, member rankTwo x = true ↔ (x = 3 ∨ x = 5 ∨ x = 6) := by decide

theorem sharp_upper_bound :
    ∀ a : Subset, Antichain a → cardinality a ≤ 3 := by decide

theorem rankOne_maximum : MaximumAntichain rankOne := by
  constructor
  · unfold Antichain; decide
  · intro a ha
    exact sharp_upper_bound a ha

theorem rankTwo_maximum : MaximumAntichain rankTwo := by
  constructor
  · unfold Antichain; decide
  · intro a ha
    exact sharp_upper_bound a ha

theorem rankOne_size : cardinality rankOne = 3 := by decide
theorem rankTwo_size : cardinality rankTwo = 3 := by decide
theorem two_maximum_antichains_differ : rankOne ≠ rankTwo := by decide

/-- Direct negation of the uniqueness clause on this chain product. -/
theorem conjecture8544_false : ¬ UniqueMaximumAntichain := by
  intro h
  exact two_maximum_antichains_differ (h rankOne rankTwo rankOne_maximum rankTwo_maximum)

#print axioms every_subset_encoded
#print axioms cube_left_inverse
#print axioms cube_right_inverse
#print axioms sharp_upper_bound
#print axioms conjecture8544_false
end Conjecture8544

