import Std

/-! Counterexample to conjecture 00000008438.
The array contains each binary word of length three as one column.
All finite enumerations below use kernel reduction (`decide`). -/
namespace Conjecture8438

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

/-- Number of columns with prescribed entries in three specified rows. -/
def occurrences {n r c : Nat} (A : Fin r → Fin c → Fin n)
    (i j k : Fin r) (x y z : Fin n) : Nat :=
  ((List.finRange c).filter fun v =>
    decide (A i v = x ∧ A j v = y ∧ A k v = z)).length

/-- The standard strength-three, index-one orthogonal array property. -/
def OA3 {n r c : Nat} (A : Fin r → Fin c → Fin n) : Prop :=
  ∀ i j k : Fin r, i ≠ j → i ≠ k → j ≠ k →
    ∀ x y z : Fin n, occurrences A i j k x y z = 1

/-- This is the t=3 specialization of the conjectured upper bound. -/
def ColumnBoundAtThree : Prop :=
  ∀ (n r c : Nat), 2 ≤ n → 3 ≤ r →
    ∀ A : Fin r → Fin c → Fin n, OA3 A → c ≤ n*n - n + 3

/-- Row i of column v is bit i of the binary expansion of v. -/
def binaryArray (i : Fin 3) (v : Fin 8) : Fin 2 :=
  ⟨(v.val / 2^i.val) % 2, Nat.mod_lt _ (by decide)⟩

/-- Full coverage, in every possible row order, is checked exactly. -/
theorem binaryArray_is_OA3 : OA3 binaryArray := by unfold OA3; decide

/-- The witness also has no repeated columns. -/
theorem binaryArray_columns_distinct :
    ∀ u v : Fin 8, (∀ i : Fin 3, binaryArray i u = binaryArray i v) → u = v := by
  decide

theorem eight_exceeds_claimed_bound : ¬ (8 ≤ 2*2 - 2 + 3) := by decide

/-- This theorem negates the conjecture's universal bound specialization. -/
theorem conjecture8438_false : ¬ ColumnBoundAtThree := by
  intro h
  exact eight_exceeds_claimed_bound
    (h 2 3 8 (by decide) (by decide) binaryArray binaryArray_is_OA3)

/-- A second witness with both alphabet size and row count equal to three:
its columns are all ternary words of length three. -/
def ternaryArray (i : Fin 3) (v : Fin 27) : Fin 3 :=
  ⟨(v.val / 3^i.val) % 3, Nat.mod_lt _ (by decide)⟩

theorem ternaryArray_is_OA3 : OA3 ternaryArray := by unfold OA3; decide

theorem ternaryArray_columns_distinct :
    ∀ u v : Fin 27, (∀ i : Fin 3, ternaryArray i u = ternaryArray i v) → u = v := by
  decide

theorem conjecture8438_false_ternary : ¬ ColumnBoundAtThree := by
  intro h
  have impossible : 27 ≤ 3*3 - 3 + 3 :=
    h 3 3 27 (by decide) (by decide) ternaryArray ternaryArray_is_OA3
  exact (by decide : ¬ (27 ≤ 3*3 - 3 + 3)) impossible

#print axioms ternaryArray_is_OA3
#print axioms ternaryArray_columns_distinct
#print axioms conjecture8438_false_ternary
#print axioms binaryArray_is_OA3
#print axioms binaryArray_columns_distinct
#print axioms conjecture8438_false
end Conjecture8438


