import Std

namespace Conjecture426

/- The cyclic group acts by actual rotation of two positions.  Its action on
   the singleton set of all-zero words is allowed to be nonfaithful. -/
abbrev C := Bool
abbrev Position := Bool
abbrev Word := Position → Bool
def groupMul (a b : C) : C := Bool.xor a b
def rotate (g : C) (w : Word) : Word := fun i => w (groupMul i g)
def zeroWord : Word := fun _ => false
def X : List Word := [zeroWord]
def groupElements : List C := [false,true]

theorem group_laws :
    (∀ a b c, groupMul (groupMul a b) c = groupMul a (groupMul b c)) ∧
    (∀ a, groupMul false a = a ∧ groupMul a false = a) ∧
    (∀ a, groupMul a a = false) := by decide

def groupPower : Nat → C
  | 0 => false
  | n+1 => groupMul (groupPower n) true

theorem generator_order_two :
    groupPower 1 ≠ false ∧ groupPower 2 = false := by decide
theorem group_cyclic : ∀ g : C, ∃ n : Nat, groupPower n = g := by
  intro g
  cases g with
  | false => exact ⟨0,rfl⟩
  | true => exact ⟨1,rfl⟩
theorem group_enumeration :
    groupElements.Nodup ∧ (∀ g : C, g ∈ groupElements) ∧
    groupElements.length = 2 := by decide

def Prime (p : Nat) : Prop := 2 ≤ p ∧ ∀ d : Nat, d ∣ p → d = 1 ∨ d = p
theorem group_order_prime : Prime groupElements.length := by
  change Prime 2
  constructor
  · decide
  · intro d hd
    have hle : d ≤ 2 := Nat.le_of_dvd (by decide) hd
    have hn : d ≠ 0 := by
      intro he
      subst d
      simp at hd
    omega

theorem rotate_identity (w : Word) : rotate false w = w := by
  funext i
  cases i <;> rfl
theorem rotate_composition (a b : C) (w : Word) :
    rotate (groupMul a b) w = rotate a (rotate b w) := by
  funext i
  cases a <;> cases b <;> cases i <;> rfl
theorem rotation_on_positions_nontrivial : groupMul false true ≠ false := by decide
theorem singleton_fixed (g : C) : rotate g zeroWord = zeroWord := rfl
theorem action_closed (g : C) (w : Word) (hw : w ∈ X) : rotate g w ∈ X := by
  have he : w = zeroWord := by simpa [X] using hw
  subst w
  simp [singleton_fixed, X]
theorem X_complete (w : Word) : w ∈ X ↔ w = zeroWord := by simp [X]
theorem X_no_duplicates : X.Nodup := by simp [X]

def equalWord (w v : Word) : Bool := (w false == v false) && (w true == v true)
theorem equalWord_correct (w v : Word) : equalWord w v = true ↔ w = v := by
  constructor
  · intro h
    have h' : w false = v false ∧ w true = v true := by simpa [equalWord] using h
    funext i
    cases i with
    | false => exact h'.1
    | true => exact h'.2
  · intro h
    subst v
    simp [equalWord]
def fixedCount (g : C) : Nat := (X.filter (fun w => equalWord (rotate g w) w)).length
theorem fixed_count (g : C) : fixedCount g = 1 := rfl

/- Coefficients in ascending degree: this is the honest constant polynomial 1.
   Evaluation is proved over EVERY algebra with the stated elementary laws,
   hence applies in particular to C and to all complex roots of unity. -/
def polynomial : List Nat := [1]
structure EvaluationAlgebra (R : Type) where
  zero : R
  one : R
  add : R → R → R
  mul : R → R → R
  fromNat : Nat → R
  nat_one : fromNat 1 = one
  mul_zero : ∀ q, mul q zero = zero
  add_zero : ∀ q, add q zero = q

def evaluate {R : Type} (A : EvaluationAlgebra R) (q : R) : List Nat → R
  | [] => A.zero
  | a::as => A.add (A.fromNat a) (A.mul q (evaluate A q as))
theorem polynomial_one_at_every_point {R : Type} (A : EvaluationAlgebra R) (q : R) :
    evaluate A q polynomial = A.one := by
  simp only [polynomial,evaluate,A.mul_zero,A.add_zero,A.nat_one]

def root (g : C) : Int := if g then -1 else 1
theorem roots_are_primitive_and_faithful :
    root false = 1 ∧ root true ≠ 1 ∧ root true * root true = 1 ∧
    (∀ a b, root (groupMul a b) = root a * root b) ∧
    (∀ a b, root a = root b → a = b) := by decide

def CyclicSieving {R : Type} (A : EvaluationAlgebra R) (omega : C → R) : Prop :=
  ∀ g, evaluate A (omega g) polynomial = A.fromNat (fixedCount g)
theorem cyclic_sieving_for_every_evaluation {R : Type}
    (A : EvaluationAlgebra R) (omega : C → R) : CyclicSieving A omega := by
  intro g
  rw [polynomial_one_at_every_point, fixed_count, A.nat_one]

def intAlgebra : EvaluationAlgebra Int where
  zero := 0
  one := 1
  add := (· + ·)
  mul := (· * ·)
  fromNat := Int.ofNat
  nat_one := rfl
  mul_zero := Int.mul_zero
  add_zero := Int.add_zero

theorem conjecture426 :
    Prime groupElements.length ∧ groupElements.length = 2 ∧
    X.length = 1 ∧ CyclicSieving intAlgebra root ∧
    (∀ q : Int, evaluate intAlgebra q polynomial = 1) := by
  exact ⟨group_order_prime,rfl,rfl,cyclic_sieving_for_every_evaluation _ _,
    polynomial_one_at_every_point _⟩

/- At the identity, CSP and value 1 force |X|=1.  Thus the parenthetical
   description in the problem cannot mean nontrivial cardinality. -/
theorem identity_forces_singleton (cardinality fixedIdentity : Nat) (value : Int)
    (identityFixesAll : fixedIdentity = cardinality)
    (cspAtIdentity : value = Int.ofNat fixedIdentity) (valueOne : value = 1) :
    cardinality = 1 := by
  rw [identityFixesAll, valueOne] at cspAtIdentity
  exact Int.ofNat_inj.mp cspAtIdentity.symm

#print axioms group_order_prime
#print axioms cyclic_sieving_for_every_evaluation
#print axioms conjecture426
#print axioms identity_forces_singleton
end Conjecture426
