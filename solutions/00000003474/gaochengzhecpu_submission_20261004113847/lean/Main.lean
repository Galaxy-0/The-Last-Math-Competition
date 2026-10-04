import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace Conjecture3474

open Polynomial

set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

/-- A finite Boolean adjacency matrix. -/
abbrev Adj (n : ℕ) := Fin n → Fin n → Bool

/-- Symmetric and loopless: the input really describes a finite simple graph. -/
def IsSimple {n : ℕ} (A : Adj n) : Prop :=
  (∀ i, A i i = false) ∧ (∀ i j, A i j = A j i)

/-- Delete a vertex, relabeling the remaining vertices in increasing order. -/
def delete {n : ℕ} (A : Adj (n + 1)) (a : Fin (n + 1)) : Adj n :=
  fun i j => A (a.succAbove i) (a.succAbove j)

/-- The ABS pivot does not swap a and b. It toggles edges between different
nonempty adjacency classes relative to a and b, and leaves their incidences alone. -/
def pivot {n : ℕ} (A : Adj n) (a b : Fin n) : Adj n := fun i j =>
  if i = a ∨ i = b ∨ j = a ∨ j = b then A i j
  else Bool.xor (A i j)
    (Bool.xor (A i a && A j b) (A i b && A j a))

/-- Fix the lexicographically first edge for the well-defined ABS recursion. -/
def firstEdge {n : ℕ} (A : Adj n) : Option (Fin n × Fin n) :=
  ((List.finRange n).flatMap fun i => (List.finRange n).map fun j => (i, j)).find?
    fun e => decide (e.1 < e.2) && A e.1 e.2

/-- Original one-variable interlace polynomial (ABS Theorem 12):
q(E_n)=X^n and q(G)=q(G-a)+q(G^(ab)-b). The decreasing vertex count
makes this a total definition, with no fuel bound or unverified external data. -/
noncomputable def interlace : (n : ℕ) → Adj n → ℤ[X]
  | 0, _ => 1
  | n + 1, A => match firstEdge A with
    | none => X ^ (n + 1)
    | some (a, b) => interlace n (delete A a) + interlace n (delete (pivot A a b) b)

/-- The same recursion records the orders of its edgeless leaves. -/
def reductionLeaves : (n : ℕ) → Adj n → List ℕ
  | 0, _ => [0]
  | n + 1, A => match firstEdge A with
    | none => [n + 1]
    | some (a, b) => reductionLeaves n (delete A a) ++
        reductionLeaves n (delete (pivot A a b) b)

theorem interlace_eq_leaf_sum (n : ℕ) (A : Adj n) :
    interlace n A = ((reductionLeaves n A).map fun k => (X : ℤ[X]) ^ k).sum := by
  induction n with
  | zero => simp [interlace, reductionLeaves]
  | succ n ih =>
    simp only [interlace, reductionLeaves]
    split
    · simp
    · simp only [List.map_append, List.sum_append, ← ih]

def pathFive : Adj 5 := fun i j => decide (i.val + 1 = j.val ∨ j.val + 1 = i.val)

/-- Two disjoint copies of the five-vertex path on labels 0,...,9. -/
def twoPaths : Adj 10 := fun i j =>
  decide (i.val / 5 = j.val / 5 ∧ (i.val + 1 = j.val ∨ j.val + 1 = i.val))

theorem pathFive_simple : IsSimple pathFive := by unfold IsSimple; decide
theorem twoPaths_simple : IsSimple twoPaths := by unfold IsSimple; decide

theorem pathFive_leaves : reductionLeaves 5 pathFive = [1, 1, 2, 2, 2, 2, 2, 3] := by
  decide

theorem twoPaths_leaves : reductionLeaves 10 twoPaths =
    [2, 2, 3, 3, 3, 3, 3, 4, 2, 2, 3, 3, 3, 3, 3, 4,
     3, 3, 4, 4, 4, 4, 4, 5, 3, 3, 4, 4, 4, 4, 4, 5,
     3, 3, 4, 4, 4, 4, 4, 5, 3, 3, 4, 4, 4, 4, 4, 5,
     3, 3, 4, 4, 4, 4, 4, 5, 4, 4, 5, 5, 5, 5, 5, 6] := by
  decide

theorem pathFive_polynomial :
    interlace 5 pathFive = X ^ 3 + 5 * X ^ 2 + 2 * X := by
  rw [interlace_eq_leaf_sum, pathFive_leaves]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  ring

theorem twoPaths_polynomial :
    interlace 10 twoPaths = (X ^ 3 + 5 * X ^ 2 + 2 * X) ^ 2 := by
  rw [interlace_eq_leaf_sum, twoPaths_leaves]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  ring

/-- Pass from the integer coefficient polynomial to the same polynomial over R. -/
noncomputable def realInterlace (n : ℕ) (A : Adj n) : ℝ[X] :=
  (interlace n A).map (Int.castRingHom ℝ)

noncomputable def r : ℝ := (-5 - Real.sqrt 17) / 2

theorem r_quadratic : r ^ 2 + 5 * r + 2 = 0 := by
  have hs : Real.sqrt 17 ^ 2 = 17 := Real.sq_sqrt (by norm_num)
  unfold r
  nlinarith

theorem r_below_interval : r < -4 := by
  have hs : Real.sqrt 17 ^ 2 = 17 := Real.sq_sqrt (by norm_num)
  have hn := Real.sqrt_nonneg (17 : ℝ)
  have h3 : 3 < Real.sqrt 17 := by nlinarith
  unfold r
  linarith

theorem real_polynomial : realInterlace 10 twoPaths =
    (X ^ 3 + 5 * X ^ 2 + 2 * X : ℝ[X]) ^ 2 := by
  unfold realInterlace
  rw [twoPaths_polynomial]
  simp

theorem base_isRoot : (X ^ 3 + 5 * X ^ 2 + 2 * X : ℝ[X]).IsRoot r := by
  rw [Polynomial.IsRoot.def]
  simp only [eval_add, eval_pow, eval_mul, eval_X, eval_ofNat]
  nlinarith [r_quadratic, congrArg (fun z : ℝ => r * z) r_quadratic]

/-- A square linear divisor is the standard algebraic multiple-root certificate. -/
theorem repeated_root : (X - C r) ^ 2 ∣ realInterlace 10 twoPaths := by
  rw [real_polynomial]
  exact pow_dvd_pow_of_dvd (Polynomial.dvd_iff_isRoot.mpr base_isRoot) 2

theorem polynomial_nonzero : realInterlace 10 twoPaths ≠ 0 := by
  intro h
  have h2 := congrArg (fun p : ℝ[X] => p.eval 2) h
  rw [real_polynomial] at h2
  norm_num at h2

/-- The source's universal root-location clause, in the original one-variable
interlace convention. Repeated means multiplicity at least two in a nonzero polynomial. -/
def RootLocationClaim : Prop :=
  ∀ (n : ℕ) (A : Adj n), IsSimple A → ∀ x : ℝ,
    realInterlace n A ≠ 0 → (X - C x) ^ 2 ∣ realInterlace n A → -4 ≤ x ∧ x ≤ 0

theorem counterexample :
    IsSimple twoPaths ∧ realInterlace 10 twoPaths ≠ 0 ∧
      (X - C r) ^ 2 ∣ realInterlace 10 twoPaths ∧ r < -4 :=
  ⟨twoPaths_simple, polynomial_nonzero, repeated_root, r_below_interval⟩

theorem conjecture_false : ¬ RootLocationClaim := by
  intro h
  have hr := h 10 twoPaths twoPaths_simple r polynomial_nonzero repeated_root
  exact (not_le_of_gt r_below_interval) hr.1

#print axioms pathFive_simple
#print axioms twoPaths_simple
#print axioms pathFive_polynomial
#print axioms twoPaths_polynomial
#print axioms interlace_eq_leaf_sum
#print axioms repeated_root
#print axioms polynomial_nonzero
#print axioms counterexample
#print axioms conjecture_false

end Conjecture3474
