import Std

/-!
Counterexample to the explicit even-order assertion in conjecture 00000006334.
A weighing matrix W(n,k) has entries in {0,1,-1} and WW^T = k I.
The primary witness is a circulant W(7,4), of positive nonfull weight and odd
order. Its order also satisfies 7 >= 4+2, so it does not use the ambiguous
interpretation of the conjecture's "window" lower bound.
The older conference W(4,3) witness is retained only as a supplementary result.
-/
namespace Conjecture06334

def Matrix (n : Nat) := Fin n → Fin n → Int

-- Entry (i,j) of W W^T: the dot product of rows i and j, with all n columns.
def rowInnerProduct {n : Nat} (W : Matrix n) (i j : Fin n) : Int :=
  (List.finRange n).foldl (fun s t => s + W i t * W j t) 0

def IsWeighingMatrix {n : Nat} (k : Nat) (W : Matrix n) : Prop :=
  (∀ i j, W i j = 0 ∨ W i j = 1 ∨ W i j = -1) ∧
  (∀ i j, rowInnerProduct W i j = if i = j then (k : Int) else 0)

-- First row (1,-1,-1,0,-1,0,0), shifted cyclically to the right in each row.
def firstRow7 (j : Fin 7) : Int :=
  match j.val with
  | 0 => 1
  | 1 => -1
  | 2 => -1
  | 4 => -1
  | _ => 0

def W7 (i j : Fin 7) : Int :=
  firstRow7 ⟨(j.val + 7 - i.val) % 7, Nat.mod_lt _ (by decide)⟩

-- This identity also verifies that the displayed matrix in proof.tex is W7.
theorem W7_displayed_rows :
    (List.finRange 7).map (fun i => (List.finRange 7).map (W7 i)) =
      [[1,-1,-1,0,-1,0,0],
       [0,1,-1,-1,0,-1,0],
       [0,0,1,-1,-1,0,-1],
       [-1,0,0,1,-1,-1,0],
       [0,-1,0,0,1,-1,-1],
       [-1,0,-1,0,0,1,-1],
       [-1,-1,0,-1,0,0,1]] := by decide

theorem W7_entries :
    ∀ i j, W7 i j = 0 ∨ W7 i j = 1 ∨ W7 i j = -1 := by decide

-- All 49 row-pair inner products, each over all 7 columns, are checked.
theorem W7_orthogonality :
    ∀ i j, rowInnerProduct W7 i j = if i = j then 4 else 0 := by decide

theorem W7_is_weighing : IsWeighingMatrix 4 W7 :=
  ⟨W7_entries, W7_orthogonality⟩

theorem W7_odd_order : (7 : Nat) % 2 = 1 := by decide

-- The witness has positive, strictly submaximal weight; it even satisfies
-- the source's proposed lower bound on order, if that bound is imposed.
theorem odd_order_counterexample :
    ∃ (n k : Nat) (W : Matrix n),
      0 < k ∧ k < n ∧ k + 2 ≤ n ∧ IsWeighingMatrix k W ∧ n % 2 = 1 := by
  exact ⟨7, 4, W7, by decide, by decide, by decide, W7_is_weighing, W7_odd_order⟩

-- A direct necessary consequence of the explicit source phrase "matrix
-- order, even"; no definition of a "window" is used in this predicate.
def ClaimedEvenOrder : Prop :=
  ∀ (n k : Nat) (W : Matrix n), IsWeighingMatrix k W → n % 2 = 0

theorem claimed_even_order_false : ¬ ClaimedEvenOrder := by
  intro h
  have impossible : (7 : Nat) % 2 = 0 := h 7 4 W7 W7_is_weighing
  exact (by decide : ¬ (7 : Nat) % 2 = 0) impossible

-- Restricting to positive nonfull weights and n >= k+2 still does not help.
theorem even_order_claim_fails_under_bound :
    ¬ ∀ (n k : Nat) (W : Matrix n),
      0 < k → k < n → k + 2 ≤ n → IsWeighingMatrix k W → n % 2 = 0 := by
  intro h
  have impossible : (7 : Nat) % 2 = 0 :=
    h 7 4 W7 (by decide) (by decide) (by decide) W7_is_weighing
  exact (by decide : ¬ (7 : Nat) % 2 = 0) impossible

-- The original statement conjoins even order with its other assertions.
-- Their content is irrelevant to a conjunction whose even-order part is false.
theorem full_conjecture_false (OtherAssertions : Prop) :
    ¬ (ClaimedEvenOrder ∧ OtherAssertions) := by
  intro h
  exact claimed_even_order_false h.1

/- Supplementary counterexample to a specific interpretation of "window".
   None of the primary results above depends on these declarations. -/

def IsConferenceMatrix {n : Nat} (W : Matrix n) : Prop :=
  IsWeighingMatrix (n - 1) W ∧
  (∀ i, W i i = 0) ∧
  (∀ i j, i ≠ j → W i j = 1 ∨ W i j = -1)

def C4 (i j : Fin 4) : Int :=
  match i.val, j.val with
  | 0, 0 => 0
  | 0, _ => 1
  | 1, 0 => -1
  | 1, 1 => 0
  | 1, 2 => -1
  | 1, _ => 1
  | 2, 0 => -1
  | 2, 1 => 1
  | 2, 2 => 0
  | 2, _ => -1
  | _, 0 => -1
  | _, 1 => -1
  | _, 2 => 1
  | _, _ => 0

theorem C4_entries : ∀ i j, C4 i j = 0 ∨ C4 i j = 1 ∨ C4 i j = -1 := by decide

theorem C4_orthogonality :
    ∀ i j, rowInnerProduct C4 i j = if i = j then 3 else 0 := by decide

theorem C4_is_weighing : IsWeighingMatrix 3 C4 := by
  exact ⟨C4_entries, C4_orthogonality⟩

theorem C4_is_conference : IsConferenceMatrix C4 := by
  exact ⟨C4_is_weighing, by decide, by decide⟩

theorem C4_is_skew_symmetric : ∀ i j, C4 i j = -C4 j i := by decide

def ClaimedNecessaryBound : Prop :=
  ∀ (n k : Nat) (_ : 0 < k) (_ : k < n) (_ : n % 2 = 0)
    (W : Matrix n), IsWeighingMatrix k W → k + 2 ≤ n

theorem claimed_necessary_bound_false : ¬ ClaimedNecessaryBound := by
  intro h
  have impossible : 3 + 2 ≤ 4 := h 4 3 (by decide) (by decide) (by decide) C4 C4_is_weighing
  exact (by decide : ¬ 3 + 2 ≤ 4) impossible

-- The counterexample lies even in the conference subclass explicitly named
-- in the conjecture, so restricting to that subclass cannot repair the bound.
theorem conference_bound_false :
    ¬ ∀ (n k : Nat) (W : Matrix n), 0 < k → k < n → n % 2 = 0 →
      IsWeighingMatrix k W → IsConferenceMatrix W → k + 2 ≤ n := by
  intro h
  have impossible : 3 + 2 ≤ 4 :=
    h 4 3 C4 (by decide) (by decide) (by decide) C4_is_weighing C4_is_conference
  exact (by decide : ¬ 3 + 2 ≤ 4) impossible

-- Other assertions about an explicit square-decomposition criterion or
-- optimality cannot make a conjunction containing the false bound true.
theorem full_bound_conjecture_false (OtherAssertions : Prop) :
    ¬ (OtherAssertions ∧ ClaimedNecessaryBound) := by
  intro h
  exact claimed_necessary_bound_false h.2

#print axioms W7_displayed_rows
#print axioms W7_entries
#print axioms W7_orthogonality
#print axioms W7_is_weighing
#print axioms W7_odd_order
#print axioms odd_order_counterexample
#print axioms claimed_even_order_false
#print axioms even_order_claim_fails_under_bound
#print axioms full_conjecture_false
#print axioms C4_is_weighing
#print axioms C4_is_conference
#print axioms claimed_necessary_bound_false
#print axioms conference_bound_false
#print axioms full_bound_conjecture_false
end Conjecture06334

