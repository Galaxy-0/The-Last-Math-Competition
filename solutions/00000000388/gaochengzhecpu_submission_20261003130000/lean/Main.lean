import Std

/-!
The threshold definition of W_m forces W_k ⊆ W_m whenever m ≤ k.
No number-theoretic property of the approximation orders is needed.
Values are represented by their upward-closed sets of rational upper bounds.
-/

namespace Conjecture388

structure PositiveNat where
  val : Nat
  positive : 0 < val
deriving DecidableEq

def one : PositiveNat := ⟨1, by decide⟩
def two : PositiveNat := ⟨2, by decide⟩

/-- The nonnegative rational number num / den; reduction is unnecessary. -/
structure RationalBound where
  num : Nat
  den : Nat
  positive : 0 < den

/-- Exact comparison of fractions with positive denominators. -/
def BoundLE (q r : RationalBound) : Prop := q.num * r.den ≤ r.num * q.den

def threshold (n : Nat) (m : PositiveNat) : RationalBound :=
  ⟨n, m.val, m.positive⟩

theorem threshold_antitone (n : Nat) (m k : PositiveNat) (h : m.val ≤ k.val) :
    BoundLE (threshold n k) (threshold n m) := by
  exact Nat.mul_le_mul_left n h

/-- The comparisons v ≤ q, allowing real values or +∞.
Only upward closure is required, so the result also holds for more general cuts. -/
structure UpperCut where
  contains : RationalBound → Prop
  upward : ∀ q r, BoundLE q r → contains q → contains r

/-- Equivalent rational representations give exactly the same comparison. -/
theorem UpperCut.respects_equivalent (c : UpperCut) (q r : RationalBound)
    (h : q.num * r.den = r.num * q.den) : c.contains q ↔ c.contains r := by
  constructor
  · exact c.upward q r (Nat.le_of_eq h)
  · exact c.upward r q (Nat.le_of_eq h.symm)

/-- General interface for ordered numerical values containing rational bounds.
For real or extended-real values these are transitivity and the ordinary
order-preserving interpretation of nonnegative rational numbers. -/
structure OrderedValues (V : Type u) where
  le : V → V → Prop
  trans : ∀ {a b c}, le a b → le b c → le a c
  ofBound : RationalBound → V
  ofBound_mono : ∀ {q r}, BoundLE q r → le (ofBound q) (ofBound r)

def cutOfValue {V : Type u} (v : OrderedValues V) (a : V) : UpperCut where
  contains q := v.le a (v.ofBound q)
  upward _ _ h ha := v.trans ha (v.ofBound_mono h)

theorem cutOfValue_exact {V : Type u} (v : OrderedValues V) (a : V)
    (q : RationalBound) :
    (cutOfValue v a).contains q ↔ v.le a (v.ofBound q) := Iff.rfl

/-- For subsets of Nat, having witnesses above every bound is infinitude. -/
def InfinitelyOften (p : Nat → Prop) : Prop := ∀ B, ∃ n, B < n ∧ p n

theorem InfinitelyOften.mono {p q : Nat → Prop} (h : ∀ n, p n → q n)
    (hp : InfinitelyOften p) : InfinitelyOften q := by
  intro B
  obtain ⟨n, hn, hp⟩ := hp B
  exact ⟨n, hn, h n hp⟩

/-- Every excluded class U_k uses a positive integer index. -/
def NoU {X : Type u} (U : PositiveNat → X → Prop) (x : X) : Prop :=
  ∀ k, ¬ U k x

/-- The source definition, with the same approximation orders and U_k for all m. -/
def W {X : Type u} (orders : X → Nat → UpperCut)
    (U : PositiveNat → X → Prop) (m : PositiveNat) (x : X) : Prop :=
  NoU U x ∧ InfinitelyOften (fun n => (orders x n).contains (threshold n m))

theorem W_antitone {X : Type u} (orders : X → Nat → UpperCut)
    (U : PositiveNat → X → Prop) (m k : PositiveNat) (h : m.val ≤ k.val)
    (x : X) : W orders U k x → W orders U m x := by
  rintro ⟨hU, hInf⟩
  refine ⟨hU, InfinitelyOften.mono ?_ hInf⟩
  intro n hn
  exact (orders x n).upward _ _ (threshold_antitone n m k h) hn

theorem W_two_subset_W_one {X : Type u} (orders : X → Nat → UpperCut)
    (U : PositiveNat → X → Prop) (x : X) :
    W orders U two x → W orders U one x :=
  W_antitone orders U one two (by decide) x

def PairwiseDisjoint {X : Type u} (orders : X → Nat → UpperCut)
    (U : PositiveNat → X → Prop) : Prop :=
  ∀ m k, m ≠ k → ∀ x, ¬ (W orders U m x ∧ W orders U k x)

def EveryClassNonempty {X : Type u} (orders : X → Nat → UpperCut)
    (U : PositiveNat → X → Prop) : Prop :=
  ∀ m, ∃ x, W orders U m x

theorem disjoint_forces_W_two_empty {X : Type u} (orders : X → Nat → UpperCut)
    (U : PositiveNat → X → Prop) (h : PairwiseDisjoint orders U) :
    ¬ ∃ x, W orders U two x := by
  rintro ⟨x, hx⟩
  exact h one two (by decide) x ⟨W_two_subset_W_one orders U x hx, hx⟩

/-- Negates two necessary clauses of the source claim, for every possible
approximation-order assignment, every underlying set, and every family U_k. -/
theorem conjecture388_refuted {X : Type u} (orders : X → Nat → UpperCut)
    (U : PositiveNat → X → Prop) :
    ¬ (EveryClassNonempty orders U ∧ PairwiseDisjoint orders U) := by
  rintro ⟨hNonempty, hDisjoint⟩
  exact disjoint_forces_W_two_empty orders U hDisjoint (hNonempty two)

/-- Same conclusion expressed directly through comparisons in an ordered
numerical value type; this is the semantic bridge for ordinary w_n values. -/
theorem ordered_value_version {X : Type u} {V : Type v}
    (v : OrderedValues V) (orders : X → Nat → V) (U : PositiveNat → X → Prop) :
    ¬ ((∀ m, ∃ x, NoU U x ∧
          InfinitelyOften (fun n => v.le (orders x n) (v.ofBound (threshold n m)))) ∧
       (∀ m k, m ≠ k → ∀ x,
          ¬ ((NoU U x ∧ InfinitelyOften (fun n =>
                 v.le (orders x n) (v.ofBound (threshold n m)))) ∧
             (NoU U x ∧ InfinitelyOften (fun n =>
                 v.le (orders x n) (v.ofBound (threshold n k))))))) := by
  exact conjecture388_refuted (fun x n => cutOfValue v (orders x n)) U

#print axioms conjecture388_refuted
#print axioms ordered_value_version

end Conjecture388
