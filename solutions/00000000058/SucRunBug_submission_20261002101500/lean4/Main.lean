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
namespace TLMC58
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

theorem violates_bound (c : ℝ) (hc : 1 < c) :
    ¬ c ^ 2 ≤ ((transversals additionSquare).card : ℝ) := by
  rw [no_transversals, Nat.cast_zero]
  have : 0 < c ^ 2 := sq_pos_of_pos (by linarith)
  linarith
#print axioms latin
#print axioms no_transversals
#print axioms violates_bound
end TLMC58
