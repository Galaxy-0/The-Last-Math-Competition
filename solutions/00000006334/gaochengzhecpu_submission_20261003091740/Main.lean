import Std

/-!
Complete finite counterexample to conjecture 00000006334.
A weighing matrix W(n,k) has entries in {0,1,-1} and WW^T = k I.
The explicit conference matrix below is W(4,3), contradicting the claimed
necessary lower bound n >= k+2. It also has 0<k<n and even positive order.
-/
namespace Conjecture06334

def Matrix (n : Nat) := Fin n → Fin n → Int

def rowInnerProduct {n : Nat} (W : Matrix n) (i j : Fin n) : Int :=
  (List.finRange n).foldl (fun s t => s + W i t * W j t) 0

def IsWeighingMatrix {n : Nat} (k : Nat) (W : Matrix n) : Prop :=
  (∀ i j, W i j = 0 ∨ W i j = 1 ∨ W i j = -1) ∧
  (∀ i j, rowInnerProduct W i j = if i = j then (k : Int) else 0)

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
theorem full_conjecture_false (OtherAssertions : Prop) :
    ¬ (OtherAssertions ∧ ClaimedNecessaryBound) := by
  intro h
  exact claimed_necessary_bound_false h.2

#print axioms C4_is_weighing
#print axioms C4_is_conference
#print axioms claimed_necessary_bound_false
#print axioms full_conjecture_false
end Conjecture06334

