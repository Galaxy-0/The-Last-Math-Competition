import Mathlib

/-!
# Conjecture 00000002060

The cyclic group of order 12 is represented by the additive group of `ZMod 12`,
wrapped as a multiplicative group. Its order is neither a prime power nor
squarefree, contradicting the claimed description of finite group orders.
-/

namespace Submission00000002060

/-- An order occurs in the spectrum of finite groups when an actual finite
carrier with a group structure has that cardinality. -/
def FiniteGroupOrderOccurs (n : ℕ) : Prop :=
  ∃ (G : Type) (_ : Group G) (_ : Fintype G), Fintype.card G = n

/-- The spectrum of the variety of groups, stated as a set of natural numbers. -/
def finiteGroupSpectrum : Set ℕ := {n | FiniteGroupOrderOccurs n}

/-- The additive cyclic group on `ZMod 12`, viewed as a multiplicative group. -/
abbrev cyclicGroup12 := Multiplicative (ZMod 12)

/-- This is an actual group with exactly twelve elements. -/
theorem cyclicGroup12_order : FiniteGroupOrderOccurs 12 := by
  refine ⟨cyclicGroup12, inferInstance, inferInstance, ?_⟩
  simp [cyclicGroup12]

/-- A prime power uses a prime base and a positive exponent. -/
def IsPrimePower (n : ℕ) : Prop :=
  ∃ p k : ℕ, Nat.Prime p ∧ 0 < k ∧ p ^ k = n

/-- Twelve is not a prime power. If a prime power equals 12, its prime base
must divide 12 and hence be 2 or 3; neither can have a power equal to 12. -/
theorem twelve_not_prime_power : ¬ IsPrimePower 12 := by
  rintro ⟨p, k, hp, hk, heq⟩
  have hpowdvd : p ∣ p ^ k := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    simp [pow_succ]
  have hpdiv : p ∣ 12 := by rw [← heq]; exact hpowdvd
  have hple : p ≤ 12 := Nat.le_of_dvd (by norm_num) hpdiv
  have hpval : p = 2 ∨ p = 3 := by
    interval_cases p <;> norm_num at *
  rcases hpval with hp2 | hp3
  · subst p
    have h3 : 3 ∣ 2 ^ k := by rw [heq]; norm_num
    have h3p := (show Nat.Prime 3 by norm_num).dvd_of_dvd_pow h3
    norm_num at h3p
  · subst p
    have h2 : 2 ∣ 3 ^ k := by rw [heq]; norm_num
    have h2p := (show Nat.Prime 2 by norm_num).dvd_of_dvd_pow h2
    norm_num at h2p

/-- Twelve is not squarefree, because the square of 2 divides it. -/
theorem twelve_not_squarefree : ¬ Squarefree (12 : ℕ) := by
  intro hs
  have hdiv : 2 ^ 2 ∣ (12 : ℕ) := by norm_num
  have hfac : 2 ≤ Nat.factorization 12 2 :=
    (Nat.Prime.pow_dvd_iff_le_factorization (by norm_num) (by norm_num)).1 hdiv
  have hone : Nat.factorization 12 2 ≤ 1 :=
    (Nat.squarefree_iff_factorization_le_one (by norm_num)).1 hs 2
  omega

/-- The proposed description permits only prime powers or squarefree orders. -/
def PrimePowerOrSquarefree (n : ℕ) : Prop :=
  IsPrimePower n ∨ Squarefree n

/-- The conjectured exclusion of all other finite group orders. -/
def ClaimedSpectrumDescription : Prop :=
  ∀ n, n ∈ finiteGroupSpectrum → PrimePowerOrSquarefree n

/-- The cyclic group of order 12 is an explicit counterexample to the claimed
spectrum description: 12 is an occurring finite group order, but neither a
prime power nor squarefree. -/
theorem conjecture_00000002060_false : ¬ ClaimedSpectrumDescription := by
  intro h
  have h12 : 12 ∈ finiteGroupSpectrum := cyclicGroup12_order
  have hallowed : PrimePowerOrSquarefree 12 := h 12 h12
  exact hallowed.elim twelve_not_prime_power twelve_not_squarefree

#print axioms conjecture_00000002060_false

end Submission00000002060
