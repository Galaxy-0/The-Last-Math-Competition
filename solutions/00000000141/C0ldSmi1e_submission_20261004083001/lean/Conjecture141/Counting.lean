import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Data.Fintype.Perm
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic

/-! The actual number of permutations with prime cycle lengths has a factorial lower bound.
The cycle partition includes fixed points, so a fixed point contributes the nonprime part `1`. -/

noncomputable section
open Equiv Equiv.Perm

namespace Conjecture141

/-- Every cycle length, including lengths of fixed-point cycles, is prime. -/
def PrimeCycles {n : ℕ} (σ : Equiv.Perm (Fin n)) : Prop :=
  ∀ k ∈ σ.partition.parts, Nat.Prime k

/-- The cardinality of the actual finite subtype of permutations in the conjecture. -/
def N (n : ℕ) : ℕ := by
  classical
  exact Fintype.card {σ : Equiv.Perm (Fin n) // PrimeCycles σ}

/-- A permutation determines a perfect matching between two labelled copies of its domain. -/
def crossMatching {α : Type*} (σ : Equiv.Perm α) : Equiv.Perm (α ⊕ α) where
  toFun := Sum.elim (fun x => Sum.inr (σ x)) (fun x => Sum.inl (σ.symm x))
  invFun := Sum.elim (fun x => Sum.inr (σ x)) (fun x => Sum.inl (σ.symm x))
  left_inv := by intro x; cases x <;> simp
  right_inv := by intro x; cases x <;> simp

@[simp] theorem crossMatching_inl {α : Type*} (σ : Equiv.Perm α) (x : α) :
    crossMatching σ (Sum.inl x) = Sum.inr (σ x) := rfl

@[simp] theorem crossMatching_inr {α : Type*} (σ : Equiv.Perm α) (x : α) :
    crossMatching σ (Sum.inr x) = Sum.inl (σ.symm x) := rfl

@[simp] theorem crossMatching_twice {α : Type*} (σ : Equiv.Perm α) (x : α ⊕ α) :
    crossMatching σ (crossMatching σ x) = x := by
  cases x <;> simp

theorem crossMatching_no_fixed {α : Type*} (σ : Equiv.Perm α) (x : α ⊕ α) :
    crossMatching σ x ≠ x := by
  cases x <;> simp

theorem crossMatching_injective {α : Type*} :
    Function.Injective (crossMatching : Equiv.Perm α → Equiv.Perm (α ⊕ α)) := by
  intro σ τ h
  ext x
  have hx := congrArg (fun f : Equiv.Perm (α ⊕ α) => f (Sum.inl x)) h
  simpa using hx

/-- Relabel the disjoint union by exactly `2 * n` elements. -/
def doubleFinEquiv (n : ℕ) : Fin n ⊕ Fin n ≃ Fin (2 * n) :=
  finSumFinEquiv.trans (finCongr (by omega))

def matchingPermutation {n : ℕ} (σ : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (2 * n)) :=
  (doubleFinEquiv n).permCongr (crossMatching σ)

theorem matchingPermutation_no_fixed {n : ℕ} (σ : Equiv.Perm (Fin n))
    (x : Fin (2 * n)) : matchingPermutation σ x ≠ x := by
  intro h
  have hx := congrArg (doubleFinEquiv n).symm h
  have hfixed : crossMatching σ ((doubleFinEquiv n).symm x) =
      (doubleFinEquiv n).symm x := by
    simpa [matchingPermutation] using hx
  exact crossMatching_no_fixed σ _ hfixed

theorem matchingPermutation_sq {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    matchingPermutation σ ^ 2 = 1 := by
  ext x
  simp [pow_two, matchingPermutation, Equiv.Perm.mul_apply]

theorem matchingPermutation_injective (n : ℕ) :
    Function.Injective (matchingPermutation : Equiv.Perm (Fin n) → Equiv.Perm (Fin (2 * n))) := by
  intro σ τ h
  exact crossMatching_injective ((doubleFinEquiv n).permCongr.injective h)

/-- A fixed-point-free involution has only cycles of length two, hence only prime cycles. -/
theorem primeCycles_of_involution_no_fixed {n : ℕ} {σ : Equiv.Perm (Fin n)}
    (hsq : σ ^ 2 = 1) (hfixed : ∀ x, σ x ≠ x) : PrimeCycles σ := by
  have hsupp : σ.support = Finset.univ := by
    apply Finset.eq_univ_iff_forall.mpr
    intro x
    exact Equiv.Perm.mem_support.mpr (hfixed x)
  intro k hk
  rw [Equiv.Perm.parts_partition, hsupp] at hk
  simp only [Finset.card_univ, Nat.sub_self, Multiset.replicate_zero, add_zero] at hk
  have hk_dvd : k ∣ 2 :=
    (Equiv.Perm.dvd_of_mem_cycleType hk).trans (orderOf_dvd_of_pow_eq_one hsq)
  have hk_eq : k = 2 :=
    le_antisymm (Nat.le_of_dvd (by norm_num) hk_dvd) (Equiv.Perm.two_le_of_mem_cycleType hk)
  rw [hk_eq]
  exact Nat.prime_two

theorem matchingPermutation_primeCycles {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    PrimeCycles (matchingPermutation σ) :=
  primeCycles_of_involution_no_fixed (matchingPermutation_sq σ) (matchingPermutation_no_fixed σ)

/-- The injection used for the counting lower bound, with the prime-cycle proof in its codomain. -/
def matchingEmbedding (n : ℕ) :
    Equiv.Perm (Fin n) ↪ {σ : Equiv.Perm (Fin (2 * n)) // PrimeCycles σ} where
  toFun σ := ⟨matchingPermutation σ, matchingPermutation_primeCycles σ⟩
  inj' := by
    intro σ τ h
    exact matchingPermutation_injective n (congrArg Subtype.val h)

/-- At least `n!` permutations on `2n` labelled elements have all cycle lengths prime. -/
theorem factorial_le_count_even (n : ℕ) : n.factorial ≤ N (2 * n) := by
  classical
  simpa [N, Fintype.card_perm] using
    Fintype.card_le_of_injective (matchingEmbedding n) (matchingEmbedding n).injective

end Conjecture141
