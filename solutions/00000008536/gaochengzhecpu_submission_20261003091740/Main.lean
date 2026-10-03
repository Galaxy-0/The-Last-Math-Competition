import Std

/-! B_6 has six join-irreducibles but can be generated as a pure lattice
by four sets: the four vertex stars of K_4 on its six edges. -/
namespace Conjecture8536
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

abbrev Element := Fin 64

def bit (x : Element) (i : Fin 6) : Bool := (x.val / 2^i.val) % 2 == 1

def meet (x y : Element) : Element :=
  ⟨(x.val &&& y.val) % 64, Nat.mod_lt _ (by decide)⟩

def join (x y : Element) : Element :=
  ⟨(x.val ||| y.val) % 64, Nat.mod_lt _ (by decide)⟩

/-- The operations are intersection and union of six-element subsets. -/
theorem meet_bits : ∀ x y : Element, ∀ i : Fin 6,
    bit (meet x y) i = (bit x i && bit y i) := by decide

theorem join_bits : ∀ x y : Element, ∀ i : Fin 6,
    bit (join x y) i = (bit x i || bit y i) := by decide

theorem bits_injective : ∀ x y : Element,
    (∀ i : Fin 6, bit x i = bit y i) → x = y := by decide

/-- Algebraic axioms defining a distributive lattice (no constants used). -/
def DistributiveLatticeLaws : Prop :=
  (∀ x y, meet x y = meet y x) ∧
  (∀ x y z, meet (meet x y) z = meet x (meet y z)) ∧
  (∀ x, meet x x = x) ∧
  (∀ x y, join x y = join y x) ∧
  (∀ x y z, join (join x y) z = join x (join y z)) ∧
  (∀ x, join x x = x) ∧
  (∀ x y, meet x (join x y) = x ∧ join x (meet x y) = x) ∧
  (∀ x y z, meet x (join y z) = join (meet x y) (meet x z))

theorem booleanSix_is_distributive_lattice : DistributiveLatticeLaws := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y
    apply bits_injective
    intro i
    simp only [meet_bits]
    cases bit x i <;> cases bit y i <;> rfl
  · intro x y z
    apply bits_injective
    intro i
    simp only [meet_bits]
    cases bit x i <;> cases bit y i <;> cases bit z i <;> rfl
  · intro x
    apply bits_injective
    intro i
    simp only [meet_bits]
    cases bit x i <;> rfl
  · intro x y
    apply bits_injective
    intro i
    simp only [join_bits]
    cases bit x i <;> cases bit y i <;> rfl
  · intro x y z
    apply bits_injective
    intro i
    simp only [join_bits]
    cases bit x i <;> cases bit y i <;> cases bit z i <;> rfl
  · intro x
    apply bits_injective
    intro i
    simp only [join_bits]
    cases bit x i <;> rfl
  · intro x y
    constructor
    · apply bits_injective
      intro i
      simp only [meet_bits, join_bits]
      cases bit x i <;> cases bit y i <;> rfl
    · apply bits_injective
      intro i
      simp only [meet_bits, join_bits]
      cases bit x i <;> cases bit y i <;> rfl
  · intro x y z
    apply bits_injective
    intro i
    simp only [meet_bits, join_bits]
    cases bit x i <;> cases bit y i <;> cases bit z i <;> rfl

/-- Zero really is the bottom element for the lattice order. -/
theorem zero_is_bottom : ∀ x : Element, meet 0 x = 0 ∧ join 0 x = x := by decide

/-- Standard finite-lattice definition of a nonzero join-irreducible. -/
def JoinIrreducible (x : Element) : Prop :=
  x ≠ 0 ∧ ∀ a b : Element, join a b = x → a = x ∨ b = x

instance (x : Element) : Decidable (JoinIrreducible x) := by
  unfold JoinIrreducible
  infer_instance

theorem join_irreducibles_exact : ∀ x : Element,
    JoinIrreducible x ↔ (x = 1 ∨ x = 2 ∨ x = 4 ∨ x = 8 ∨ x = 16 ∨ x = 32) := by
  decide

def joinIrreducibleCount : Nat :=
  ((List.finRange 64).filter fun x => decide (JoinIrreducible x)).length

theorem join_irreducible_count_six : joinIrreducibleCount = 6 := by decide

/-- Terms in the pure lattice language; bottom and top are not primitives. -/
inductive Term (k : Nat) where
  | var : Fin k → Term k
  | inf : Term k → Term k → Term k
  | sup : Term k → Term k → Term k

def evaluate {k : Nat} (g : Fin k → Element) : Term k → Element
  | .var i => g i
  | .inf a b => meet (evaluate g a) (evaluate g b)
  | .sup a b => join (evaluate g a) (evaluate g b)

def Generates {k : Nat} (g : Fin k → Element) : Prop :=
  ∀ x : Element, ∃ t : Term k, evaluate g t = x

/-- Edges are 01,02,03,12,13,23. The generators are their vertex stars. -/
def generators (i : Fin 4) : Element :=
  match i.val with
  | 0 => 7
  | 1 => 25
  | 2 => 42
  | _ => 52

def zeroTerm : Term 4 := .inf (.inf (.var 0) (.var 1)) (.var 2)

def atomTerm (i : Fin 6) : Term 4 :=
  match i.val with
  | 0 => .inf (.var 0) (.var 1)
  | 1 => .inf (.var 0) (.var 2)
  | 2 => .inf (.var 0) (.var 3)
  | 3 => .inf (.var 1) (.var 2)
  | 4 => .inf (.var 1) (.var 3)
  | _ => .inf (.var 2) (.var 3)

theorem zero_term_correct : evaluate generators zeroTerm = 0 := by decide

theorem atom_terms_correct : ∀ i : Fin 6,
    (evaluate generators (atomTerm i)).val = 2^i.val := by decide

def canonicalTerm (x : Element) : Term 4 :=
  (List.finRange 6).foldl (fun t i => if bit x i then .sup t (atomTerm i) else t) zeroTerm

/-- Every one of the 64 lattice elements has an explicit term. -/
theorem canonical_terms_correct :
    ∀ x : Element, evaluate generators (canonicalTerm x) = x := by decide

theorem four_generators_suffice : Generates generators := by
  intro x
  exact ⟨canonicalTerm x, canonical_terms_correct x⟩

/-- If the least number of generators equals the number of join-irreducibles,
    then every generating k-tuple must satisfy this lower bound. -/
def ClaimedGeneratorLowerBound : Prop :=
  ∀ (k : Nat) (g : Fin k → Element), Generates g → joinIrreducibleCount ≤ k

theorem conjecture8536_false : ¬ ClaimedGeneratorLowerBound := by
  intro h
  have bad := h 4 generators four_generators_suffice
  rw [join_irreducible_count_six] at bad
  exact (by decide : ¬ (6 ≤ 4)) bad

#print axioms booleanSix_is_distributive_lattice
#print axioms join_irreducibles_exact
#print axioms four_generators_suffice
#print axioms conjecture8536_false
end Conjecture8536
