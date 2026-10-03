import Std

/-! Conjecture 8535: the two-element Boolean lattice is a counterexample.
This file checks the finite lattice, its geometric and supersolvable
properties, the defining Mobius recurrence and its characteristic root. -/
namespace Conjecture8535
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

structure LatticeData (n : Nat) where
  le : Fin n → Fin n → Bool
  bot : Fin n
  top : Fin n
  meet : Fin n → Fin n → Fin n
  join : Fin n → Fin n → Fin n
  rank : Fin n → Nat

def Below {n} (L : LatticeData n) (x y : Fin n) : Prop := L.le x y = true

instance {n} (L : LatticeData n) (x y : Fin n) : Decidable (Below L x y) := inferInstanceAs (Decidable (L.le x y = true))

def LatticeLaws {n} (L : LatticeData n) : Prop :=
  (∀ x, Below L x x) ∧
  (∀ x y, Below L x y → Below L y x → x = y) ∧
  (∀ x y z, Below L x y → Below L y z → Below L x z) ∧
  (∀ x, Below L L.bot x ∧ Below L x L.top) ∧
  (∀ x y, Below L (L.meet x y) x ∧ Below L (L.meet x y) y) ∧
  (∀ x y z, Below L z x → Below L z y → Below L z (L.meet x y)) ∧
  (∀ x y, Below L x (L.join x y) ∧ Below L y (L.join x y)) ∧
  (∀ x y z, Below L x z → Below L y z → Below L (L.join x y) z)

def Covers {n} (L : LatticeData n) (x y : Fin n) : Prop :=
  Below L x y ∧ x ≠ y ∧
  ∀ z, Below L x z → Below L z y → z = x ∨ z = y

instance {n} (L : LatticeData n) (x y : Fin n) : Decidable (Covers L x y) := by unfold Covers; infer_instance

def Graded {n} (L : LatticeData n) : Prop :=
  L.rank L.bot = 0 ∧ ∀ x y, Covers L x y → L.rank y = L.rank x + 1

def atomsBelow {n} (L : LatticeData n) (x : Fin n) : List (Fin n) :=
  (List.finRange n).filter fun a =>
    decide (Covers L L.bot a ∧ Below L a x)

def Atomistic {n} (L : LatticeData n) : Prop :=
  ∀ x, (atomsBelow L x).foldl L.join L.bot = x

def Semimodular {n} (L : LatticeData n) : Prop :=
  ∀ x y, Covers L (L.meet x y) x → Covers L y (L.join x y)

def Geometric {n} (L : LatticeData n) : Prop :=
  LatticeLaws L ∧ Graded L ∧ Atomistic L ∧ Semimodular L

def ModularElement {n} (L : LatticeData n) (m : Fin n) : Prop :=
  ∀ x y, Below L x y → L.join x (L.meet m y) = L.meet (L.join x m) y

def MaximalChain {n} (L : LatticeData n) (c : List (Fin n)) : Prop :=
  c.Nodup ∧
  (∀ x y, x ∈ c → y ∈ c → Below L x y ∨ Below L y x) ∧
  (∀ x, (∀ y, y ∈ c → Below L x y ∨ Below L y x) → x ∈ c)

def Supersolvable {n} (L : LatticeData n) : Prop :=
  ∃ c : List (Fin n), MaximalChain L c ∧ ∀ m, m ∈ c → ModularElement L m

/-- The defining recurrence for the values mu(bottom,x). -/
def MobiusRecurrence {n} (L : LatticeData n) (mu : Fin n → Int) : Prop :=
  ∀ x, (((List.finRange n).filter fun y => L.le y x).map mu).sum =
    if x = L.bot then 1 else 0

/-- Characteristic polynomial evaluated at an integer.
    An integer root is in particular a real root. -/
def characteristicAt {n} (L : LatticeData n) (mu : Fin n → Int) (t : Int) : Int :=
  ((List.finRange n).map fun x => mu x * t ^ (L.rank L.top - L.rank x)).sum

/-- Necessary integer-root specialization of the conjecture's first clause. -/
def NegativeRootClaim : Prop :=
  ∀ (n : Nat) (L : LatticeData n) (mu : Fin n → Int),
    Geometric L → Supersolvable L → MobiusRecurrence L mu →
    ∀ r : Int, characteristicAt L mu r = 0 → r < 0

def booleanOne : LatticeData 2 where
  le x y := decide (x.val ≤ y.val)
  bot := 0
  top := 1
  meet x y := if x.val ≤ y.val then x else y
  join x y := if x.val ≤ y.val then y else x
  rank x := x.val

def mobius (x : Fin 2) : Int := if x = 0 then 1 else -1

theorem booleanOne_geometric : Geometric booleanOne := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold LatticeLaws; decide
  · unfold Graded; decide
  · unfold Atomistic; decide
  · unfold Semimodular; decide

theorem booleanOne_supersolvable : Supersolvable booleanOne := by
  refine ⟨[0, 1], ?_, ?_⟩
  · unfold MaximalChain Below
    decide
  · unfold ModularElement Below
    decide

theorem mobius_correct : MobiusRecurrence booleanOne mobius := by
  unfold MobiusRecurrence
  decide

theorem positive_characteristic_root : characteristicAt booleanOne mobius 1 = 0 := by
  decide

theorem conjecture8535_false : ¬ NegativeRootClaim := by
  intro h
  have impossible : (1 : Int) < 0 :=
    h 2 booleanOne mobius booleanOne_geometric booleanOne_supersolvable
      mobius_correct 1 positive_characteristic_root
  exact (by decide : ¬ (1 : Int) < 0) impossible

#print axioms booleanOne_geometric
#print axioms booleanOne_supersolvable
#print axioms mobius_correct
#print axioms conjecture8535_false
end Conjecture8535


