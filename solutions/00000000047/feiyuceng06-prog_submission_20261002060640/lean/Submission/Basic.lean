import Mathlib

/-!
# Conjecture 00000000047 holds

Conjecture 00000000047 asserts that for every sufficiently large even `n` there
is a permutation `π` of `[n] = {1, …, n}` such that `π(i) + i` is prime for all
`i`. We prove more: such a permutation exists for **every** `n`, even or odd,
and it can be taken to be an involution.

The construction is by strong induction on `n`, using Bertrand's postulate. For
`n ≥ 1` choose a prime `p` with `n < p ≤ 2n` and put `m = p - n`, so
`1 ≤ m ≤ n`. The map `i ↦ p - i` is an involution of the block `{m, …, n}`,
and `(p - i) + i = p` is prime there. The remaining block `{1, …, m - 1}` has
fewer than `n` elements, and the induction hypothesis supplies the permutation on
it.
-/

namespace Submission00000000047

/-- A *prime permutation* of `[n] = {1, …, n}`: a permutation `π` of `[n]` such
that `π(i) + i` is prime for every `i ∈ [n]`. -/
def HasPrimePermutation (n : ℕ) : Prop :=
  ∃ π : Equiv.Perm (Finset.Icc 1 n), ∀ i, Nat.Prime ((π i : ℕ) + (i : ℕ))

/-- Conjecture 00000000047: for every sufficiently large even `n` there is a
prime permutation of `[n]`. -/
def ConjectureHolds : Prop :=
  ∃ N : ℕ, ∀ n, N ≤ n → Even n → HasPrimePermutation n

/-- The core construction: for every `n` there is a function `f` that maps
`[n]` into itself, is an involution on `[n]`, and has `f(i) + i` prime for every
`i ∈ [n]`. -/
theorem exists_prime_involution (n : ℕ) :
    ∃ f : ℕ → ℕ, ∀ i, 1 ≤ i → i ≤ n →
      1 ≤ f i ∧ f i ≤ n ∧ f (f i) = i ∧ Nat.Prime (f i + i) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact ⟨id, fun i h₁ h₂ => by omega⟩
    -- Bertrand: a prime `p` with `n < p ≤ 2n`; the block `[p - n, n]` pairs up.
    obtain ⟨p, hp, hnp, hp2⟩ := Nat.exists_prime_lt_and_le_two_mul n hn.ne'
    -- The induction hypothesis handles `[1, p - n - 1]`.
    obtain ⟨g, hg⟩ := ih (p - n - 1) (by omega)
    refine ⟨fun i => if p - n ≤ i then p - i else g i, ?_⟩
    intro i hi₁ hin
    by_cases hi : p - n ≤ i
    · have hfi : p - n ≤ p - i := by omega
      simp only [hi, hfi, if_true]
      refine ⟨by omega, by omega, by omega, ?_⟩
      rwa [Nat.sub_add_cancel (by omega : i ≤ p)]
    · obtain ⟨g₁, g₂, g₃, g₄⟩ := hg i hi₁ (by omega)
      have hgi : ¬ p - n ≤ g i := by omega
      simp only [hi, hgi, if_false]
      exact ⟨g₁, by omega, g₃, g₄⟩

/-- Every `n` admits a prime permutation of `[n]` (which is moreover an
involution). -/
theorem hasPrimePermutation (n : ℕ) : HasPrimePermutation n := by
  obtain ⟨f, hf⟩ := exists_prime_involution n
  have hmem : ∀ i : Finset.Icc 1 n, f i ∈ Finset.Icc 1 n := by
    rintro ⟨i, hi⟩
    rw [Finset.mem_Icc] at hi ⊢
    exact ⟨(hf i hi.1 hi.2).1, (hf i hi.1 hi.2).2.1⟩
  let g : Finset.Icc 1 n → Finset.Icc 1 n := fun i => ⟨f i, hmem i⟩
  have hg : Function.Involutive g := by
    rintro ⟨i, hi⟩
    rw [Finset.mem_Icc] at hi
    exact Subtype.ext (hf i hi.1 hi.2).2.2.1
  refine ⟨Function.Involutive.toPerm g hg, ?_⟩
  rintro ⟨i, hi⟩
  rw [Finset.mem_Icc] at hi
  exact (hf i hi.1 hi.2).2.2.2

/-- Conjecture 00000000047 holds, with threshold `N = 0`: every `n`, even or
odd, admits a prime permutation of `[n]`. -/
theorem conjecture_00000000047 : ConjectureHolds :=
  ⟨0, fun n _ _ => hasPrimePermutation n⟩

end Submission00000000047

#print axioms Submission00000000047.conjecture_00000000047
