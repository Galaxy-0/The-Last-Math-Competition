import Std

/-! The incidence algebra of the two-point chain over F₂ has nonzero
Jacobson radical.  The radical is defined as the intersection of ALL
maximal proper left ideals, not by a numerical proxy. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Conjecture2617
abbrev R := Fin 8

def mk (a b c : Bool) : R :=
  ⟨((if a then 4 else 0) + (if b then 2 else 0) + (if c then 1 else 0)) % 8,
    Nat.mod_lt _ (by decide)⟩
def a (x : R) : Bool := x.val.testBit 2
def b (x : R) : Bool := x.val.testBit 1
def c (x : R) : Bool := x.val.testBit 0
def plus (x y : R) : R := mk (a x ^^ a y) (b x ^^ b y) (c x ^^ c y)
def times (x y : R) : R := mk (a x && a y)
  ((a x && b y) ^^ (b x && c y)) (c x && c y)
def zero : R := 0
def one : R := 5
def e : R := 2

theorem ring_laws :
    (∀ x y z : R, plus (plus x y) z = plus x (plus y z)) ∧
    (∀ x y : R, plus x y = plus y x) ∧
    (∀ x : R, plus zero x = x ∧ plus x x = zero) ∧
    (∀ x y z : R, times (times x y) z = times x (times y z)) ∧
    (∀ x : R, times one x = x ∧ times x one = x) ∧
    (∀ x y z : R, times x (plus y z) = plus (times x y) (times x z)) ∧
    (∀ x y z : R, times (plus x y) z = plus (times x z) (times y z)) := by decide

/- Boolean xor and and are addition and multiplication in F₂. These
entries identify R with upper triangular 2 by 2 matrices, i.e. incidence
functions of the chain 0 ≤ 1. -/
def entry (x : R) (i j : Fin 2) : Bool :=
  if i = 0 then (if j = 0 then a x else b x)
  else (if j = 0 then false else c x)

theorem entries_supported : ∀ x : R, entry x 1 0 = false := by decide
theorem addition_is_pointwise : ∀ x y : R, ∀ i j : Fin 2,
    entry (plus x y) i j = (entry x i j ^^ entry y i j) := by decide
theorem multiplication_is_convolution : ∀ x y : R, ∀ i j : Fin 2,
    entry (times x y) i j =
      ((entry x i 0 && entry y 0 j) ^^ (entry x i 1 && entry y 1 j)) := by decide

theorem every_incidence_function (f : Fin 2 → Fin 2 → Bool) (h : f 1 0 = false) :
    ∃ x : R, ∀ i j, entry x i j = f i j := by
  refine ⟨mk (f 0 0) (f 0 1) (f 1 1), ?_⟩
  intro i j
  have hi : i = 0 ∨ i = 1 := by omega
  have hj : j = 0 ∨ j = 1 := by omega
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;>
    cases h00 : f 0 0 <;> cases h01 : f 0 1 <;> cases h11 : f 1 1 <;>
    simp [entry, mk, a, b, c, h, h00, h01, h11] <;> decide

theorem entries_injective : ∀ x y : R,
    (∀ i j : Fin 2, entry x i j = entry y i j) → x = y := by decide

structure LeftIdeal where
  mem : R → Prop
  zero_mem : mem zero
  add_mem : ∀ {x y}, mem x → mem y → mem (plus x y)
  left_mul_mem : ∀ r {x}, mem x → mem (times r x)

def Included (I J : LeftIdeal) : Prop := ∀ x, I.mem x → J.mem x
def MaximalProper (I : LeftIdeal) : Prop :=
  ¬I.mem one ∧ ∀ J : LeftIdeal, Included I J → ¬J.mem one → Included J I
def InJacobsonRadical (x : R) : Prop :=
  ∀ I : LeftIdeal, MaximalProper I → I.mem x

theorem zero_expression : plus zero (times zero e) = zero := by decide
theorem include_expression : ∀ x : R, plus x (times zero e) = x := by decide
theorem e_expression : plus zero (times one e) = e := by decide
theorem sum_expression : ∀ i j r s : R,
    plus (plus i (times r e)) (plus j (times s e)) =
      plus (plus i j) (times (plus r s) e) := by decide
theorem mul_expression : ∀ t i r : R,
    times t (plus i (times r e)) = plus (times t i) (times (times t r) e) := by decide
theorem invert_expression : ∀ i r : R,
    one = plus i (times r e) → times (plus one (times r e)) i = one := by decide

def enlarge (I : LeftIdeal) : LeftIdeal where
  mem x := ∃ i : R, I.mem i ∧ ∃ r : R, x = plus i (times r e)
  zero_mem := ⟨zero, I.zero_mem, zero, zero_expression.symm⟩
  add_mem := by
    intro x y hx hy
    rcases hx with ⟨i, hi, r, rfl⟩
    rcases hy with ⟨j, hj, s, rfl⟩
    exact ⟨plus i j, I.add_mem hi hj, plus r s, sum_expression i j r s⟩
  left_mul_mem := by
    intro t x hx
    rcases hx with ⟨i, hi, r, rfl⟩
    exact ⟨times t i, I.left_mul_mem t hi, times t r, mul_expression t i r⟩

theorem radical_contains_e : InJacobsonRadical e := by
  intro I hI
  classical
  apply Classical.byContradiction
  intro hnot
  have incl : Included I (enlarge I) := by
    intro x hx
    exact ⟨x, hx, zero, (include_expression x).symm⟩
  have he : (enlarge I).mem e := ⟨zero, I.zero_mem, one, e_expression.symm⟩
  have h1 : (enlarge I).mem one := by
    apply Classical.byContradiction
    intro hn
    exact hnot (hI.2 (enlarge I) incl hn e he)
  rcases h1 with ⟨i, hi, r, eqn⟩
  have hunit := I.left_mul_mem (plus one (times r e)) hi
  rw [invert_expression i r eqn] at hunit
  exact hI.1 hunit

theorem e_nonzero : e ≠ zero := by decide

/- A specialization of the universal zero-radical claim to this locally
finite poset would assert this proposition. -/
def ZeroRadicalClaim : Prop := ∀ x : R, InJacobsonRadical x → x = zero

theorem not_zero_radical_claim : ¬ZeroRadicalClaim := by
  intro h
  exact e_nonzero (h e radical_contains_e)

theorem chain_locally_finite : ∀ i j : Fin 2,
    ∀ k : Fin 2, i ≤ k → k ≤ j → k = 0 ∨ k = 1 := by decide

#print axioms not_zero_radical_claim
#print axioms ring_laws
#print axioms multiplication_is_convolution
#print axioms every_incidence_function
end Conjecture2617
