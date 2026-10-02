import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.Lattice.Nat
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
noncomputable section
namespace TLMC111
def IsLatin (L : Fin 2 → Fin 2 → Fin 2) : Prop :=
  (∀ i, Function.Bijective (L i)) ∧ (∀ j, Function.Bijective (fun i => L i j))
def additionSquare (i j : Fin 2) : Fin 2 := i + j
def transversals (L : Fin 2 → Fin 2 → Fin 2) : Finset (Equiv.Perm (Fin 2)) :=
  Finset.univ.filter (fun σ => Function.Injective (fun i => L i (σ i)))
theorem order_is_prime : Nat.Prime 2 := by decide
theorem latin : IsLatin additionSquare := by
  unfold IsLatin additionSquare
  decide
theorem no_transversals : (transversals additionSquare).card = 0 := by decide

def minimumCount : ℕ := sInf {n : ℕ | ∃ L, IsLatin L ∧ (transversals L).card = n}
theorem minimum_zero : minimumCount = 0 := by
  apply Nat.eq_zero_of_le_zero
  exact Nat.sInf_le ⟨additionSquare, latin, no_transversals⟩
theorem violates_bound (c : ℝ) (hc : 1 < c) : ¬ c ^ 2 ≤ (minimumCount : ℝ) := by
  rw [minimum_zero, Nat.cast_zero]
  have : 0 < c ^ 2 := sq_pos_of_pos (by linarith)
  linarith
#print axioms minimum_zero
#print axioms violates_bound
end TLMC111
