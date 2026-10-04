import Std

namespace Conjecture5135

/-- Only elementary ordered-scalar facts are used. These are hypotheses of
    universally quantified theorems, not new axioms. In particular they hold
    over the real numbers. Division is eliminated by cross multiplication. -/
structure OrderedScale (R : Type u) where
  zero : R
  one : R
  add : R → R → R
  mul : R → R → R
  le : R → R → Prop
  lt : R → R → Prop
  le_refl : ∀ x, le x x
  le_trans : ∀ {x y z}, le x y → le y z → le x z
  not_le_of_lt : ∀ {x y}, lt x y → ¬ le y x
  one_pos : lt zero one
  lt_add_right : ∀ x y, lt zero y → lt x (add x y)
  one_mul : ∀ x, mul one x = x
  cancel_positive : ∀ {a b c}, lt zero c → le (mul a c) (mul b c) → le a b

/-- An explicit standard model checks consistency of the scalar interface.
    The theorem is NOT restricted to integer-valued condition numbers. -/
def integerScale : OrderedScale Int where
  zero := 0
  one := 1
  add := (· + ·)
  mul := (· * ·)
  le := (· ≤ ·)
  lt := (· < ·)
  le_refl := fun _ => by omega
  le_trans := fun _ _ => by omega
  not_le_of_lt := fun _ _ => by omega
  one_pos := by decide
  lt_add_right := fun _ _ _ => by omega
  one_mul := Int.one_mul
  cancel_positive := fun h hmul => Int.le_of_mul_le_mul_right hmul h

def IsLUB {X : Type v} {R : Type u} (O : OrderedScale R)
    (domain : X → Prop) (value : X → R) (upper : R) : Prop :=
  (∀ x, domain x → O.le (value x) upper) ∧
  (∀ bound, (∀ x, domain x → O.le (value x) bound) → O.le upper bound)

theorem lub_mono {X : Type v} {R : Type u} (O : OrderedScale R)
    (small large : X → Prop) (value : X → R) (s l : R)
    (hsub : ∀ x, small x → large x)
    (hs : IsLUB O small value s) (hl : IsLUB O large value l) : O.le s l := by
  exact hs.2 l (fun x hx => hl.1 x (hsub x hx))

abbrev Matrix (K : Type v) (n : Nat) := Fin n → Fin n → K

/-- Equality along every anti-diagonal: the actual Hankel condition. -/
def Hankel {K : Type v} {n : Nat} (E : Matrix K n) : Prop :=
  ∀ i j k l, i.val + j.val = k.val + l.val → E i j = E k l

def UnitDirections {K : Type v} {R : Type u} {n : Nat}
    (O : OrderedScale R) (norm : Matrix K n → R) (E : Matrix K n) : Prop :=
  O.le (norm E) O.one

def HankelDirections {K : Type v} {R : Type u} {n : Nat}
    (O : OrderedScale R) (norm : Matrix K n → R) (E : Matrix K n) : Prop :=
  UnitDirections O norm E ∧ Hankel E

/-- Both condition numbers use the SAME norm ball and amplification function.
    Amplification may be the norm of any derivative, so no particular matrix
    function, base point, symbol pair, or differentiability theorem is assumed. -/
structure ConditioningProblem {K : Type v} {R : Type u}
    (O : OrderedScale R) (n : Nat) where
  norm : Matrix K n → R
  amplification : Matrix K n → R
  structured : R
  unstructured : R
  structured_spec : IsLUB O (HankelDirections O norm) amplification structured
  unstructured_spec : IsLUB O (UnitDirections O norm) amplification unstructured
  denominator_positive : O.lt O.zero unstructured

theorem condition_numbers_ordered {K : Type v} {R : Type u} {n : Nat}
    (O : OrderedScale R) (P : ConditioningProblem (K := K) O n) :
    O.le P.structured P.unstructured := by
  exact lub_mono O _ _ P.amplification _ _ (fun _ h => h.1)
    P.structured_spec P.unstructured_spec

/-- r = structured/unstructured, expressed without division. Positivity of
    the denominator is included in ConditioningProblem. -/
def IsRatio {K : Type v} {R : Type u} {n : Nat}
    (O : OrderedScale R) (P : ConditioningProblem (K := K) O n) (r : R) : Prop :=
  O.mul r P.unstructured = P.structured

theorem every_ratio_le_one {K : Type v} {R : Type u} {n : Nat}
    (O : OrderedScale R) (P : ConditioningProblem (K := K) O n)
    (r : R) (hr : IsRatio O P r) : O.le r O.one := by
  apply O.cancel_positive P.denominator_positive
  rw [O.one_mul, hr]
  exact condition_numbers_ordered O P

def AttainableRatio {K : Type v} {R : Type u} (O : OrderedScale R)
    (n : Nat) (r : R) : Prop :=
  ∃ P : ConditioningProblem (K := K) O n, IsRatio O P r

/-- Supremizing over ANY collection of such ratios still gives at most one. -/
theorem every_supremal_ratio_le_one {K : Type v} {R : Type u} {n : Nat}
    (O : OrderedScale R) (family : R → Prop) (supremum : R)
    (hf : ∀ r, family r → AttainableRatio (K := K) O n r)
    (hsup : IsLUB O family id supremum) : O.le supremum O.one := by
  apply hsup.2 O.one
  intro r hr
  obtain ⟨P, hP⟩ := hf r hr
  exact every_ratio_le_one O P r hP

def two {R : Type u} (O : OrderedScale R) : R := O.add O.one O.one

theorem one_lt_two {R : Type u} (O : OrderedScale R) : O.lt O.one (two O) :=
  O.lt_add_right O.one O.one O.one_pos

/-- Necessary instance of the claimed upper-end attainment at dimension 4,
    where sqrt(4)=2. Arbitrary admissible families are allowed. -/
def EndpointAtFour {K : Type v} {R : Type u} (O : OrderedScale R) : Prop :=
  ∃ family : R → Prop,
    (∀ r, family r → AttainableRatio (K := K) O 4 r) ∧
    IsLUB O family id (two O)

theorem conjecture_5135_endpoint_false {K : Type v} {R : Type u}
    (O : OrderedScale R) : ¬ EndpointAtFour (K := K) O := by
  rintro ⟨family, hf, hs⟩
  exact O.not_le_of_lt (one_lt_two O)
    (every_supremal_ratio_le_one O family (two O) hf hs)

#print axioms lub_mono
#print axioms condition_numbers_ordered
#print axioms every_supremal_ratio_le_one
#print axioms conjecture_5135_endpoint_false
end Conjecture5135
