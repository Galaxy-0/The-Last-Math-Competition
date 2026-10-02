import Mathlib

/-!
# Conjecture 00000000162 is false

Conjecture 00000000162 asserts that for every `n ≥ 3` there is a planar convex
`n`-gon whose side vectors all have prime squared lengths, being two-squares
vectors for primes `p ≡ 1 (mod 4)` (integer vectors `(a, b)` with
`a² + b² = p`), and sum to zero.

This fails for every odd `n`, in particular for `n = 3`, and convexity plays
no role. If `a² + b² = p` is odd, then `a + b ≡ a² + b² ≡ 1 (mod 2)`, so exactly
one coordinate of every side vector is odd. If the `n` side vectors sum to
zero, then the sum of all their coordinates is even. That sum is also a sum of
`n` odd numbers, so `n` is even.
-/

namespace Submission00000000162

open Finset

/-- The cross product `u × v = u₁ v₂ - u₂ v₁` of two plane vectors. -/
def cross (u v : ℝ × ℝ) : ℝ := u.1 * v.2 - u.2 * v.1

/-- `P 0, P 1, …, P (n-1)` are, in this cyclic order, the vertices of a convex
`n`-gon: `n ≥ 3`, and for every edge `P i → P (i+1)` (indices mod `n`) all other
vertices lie strictly on the same side of it, the same side for all edges. -/
def IsConvexPolygon {n : ℕ} (P : Fin n → ℝ × ℝ) : Prop :=
  3 ≤ n ∧
    ((∀ i j, j ≠ i → j ≠ finRotate n i → 0 < cross (P (finRotate n i) - P i) (P j - P i)) ∨
      (∀ i j, j ≠ i → j ≠ finRotate n i → cross (P (finRotate n i) - P i) (P j - P i) < 0))

/-- A two-squares vector for a prime `p ≡ 1 (mod 4)`: an integer vector `(a, b)`
with `a² + b² = p`. -/
def IsTwoSquaresVector (v : ℤ × ℤ) : Prop :=
  ∃ p : ℕ, p.Prime ∧ p % 4 = 1 ∧ v.1 ^ 2 + v.2 ^ 2 = p

/-- Conjecture 00000000162: for every `n ≥ 3` there is a planar convex `n`-gon whose
side vectors `P (i+1) - P i` are two-squares vectors for primes `p ≡ 1 (mod 4)` and
sum to zero. -/
def ConjectureHolds : Prop :=
  ∀ n, 3 ≤ n → ∃ (P : Fin n → ℝ × ℝ) (v : Fin n → ℤ × ℤ),
    IsConvexPolygon P ∧
    (∀ i, P (finRotate n i) - P i = (((v i).1 : ℝ), ((v i).2 : ℝ))) ∧
    (∀ i, IsTwoSquaresVector (v i)) ∧
    ∑ i, v i = 0

/-- A two-squares vector for a prime `p ≡ 1 (mod 4)` has odd squared length. -/
theorem odd_of_isTwoSquaresVector {v : ℤ × ℤ} (hv : IsTwoSquaresVector v) :
    Odd (v.1 ^ 2 + v.2 ^ 2) := by
  obtain ⟨p, -, hp4, hp⟩ := hv
  rw [hp, Int.odd_iff]
  omega

/-- An integer vector with odd squared length has exactly one odd coordinate:
`a + b ≡ a² + b² (mod 2)`. -/
theorem odd_add_of_odd (a b : ℤ) (h : Odd (a ^ 2 + b ^ 2)) : Odd (a + b) := by
  rw [← ZMod.intCast_eq_one_iff_odd] at h ⊢
  push_cast at h ⊢
  rwa [ZMod.pow_card, ZMod.pow_card] at h

/-- Integer vectors with odd squared lengths can sum to zero only if there is an
even number of them. -/
theorem even_of_sum_eq_zero {n : ℕ} (v : Fin n → ℤ × ℤ)
    (hodd : ∀ i, Odd ((v i).1 ^ 2 + (v i).2 ^ 2)) (hsum : ∑ i, v i = 0) : Even n := by
  have h₁ : ∑ i, (v i).1 = 0 := by simpa [Prod.fst_sum] using congrArg Prod.fst hsum
  have h₂ : ∑ i, (v i).2 = 0 := by simpa [Prod.snd_sum] using congrArg Prod.snd hsum
  have hone : ∀ i, (((v i).1 + (v i).2 : ℤ) : ZMod 2) = 1 :=
    fun i => ZMod.intCast_eq_one_iff_odd.2 (odd_add_of_odd _ _ (hodd i))
  have hz : ∑ i, (((v i).1 + (v i).2 : ℤ) : ZMod 2) = 0 := by
    rw [← Int.cast_sum, Finset.sum_add_distrib, h₁, h₂]
    simp
  simp only [hone, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one] at hz
  exact ZMod.natCast_eq_zero_iff_even.1 hz

/-- For odd `n`, no `n` two-squares vectors for primes `p ≡ 1 (mod 4)` sum to zero;
so there is no closed `n`-gon, convex or not, with such sides. -/
theorem not_exists_of_odd {n : ℕ} (hn : Odd n) :
    ¬ ∃ v : Fin n → ℤ × ℤ, (∀ i, IsTwoSquaresVector (v i)) ∧ ∑ i, v i = 0 := by
  rintro ⟨v, hv, hsum⟩
  have := even_of_sum_eq_zero v (fun i => odd_of_isTwoSquaresVector (hv i)) hsum
  exact (Nat.not_even_iff_odd.2 hn) this

/-- Conjecture 00000000162 is false: it fails for `n = 3` (and for every odd `n`). -/
theorem conjecture_00000000162_false : ¬ ConjectureHolds := by
  intro h
  obtain ⟨-, v, -, -, hv, hsum⟩ := h 3 le_rfl
  exact not_exists_of_odd (by decide) ⟨v, hv, hsum⟩

end Submission00000000162

#print axioms Submission00000000162.conjecture_00000000162_false
