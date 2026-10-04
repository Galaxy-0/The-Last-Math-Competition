import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

namespace Conjecture40

noncomputable section
open Finset

/-- The actual sumset of a finite set of real numbers. -/
def sumset (A : Finset ℝ) : Finset ℝ :=
  (A ×ˢ A).image (fun p => p.1 + p.2)

/-- The actual product set of a finite set of real numbers. -/
def productset (A : Finset ℝ) : Finset ℝ :=
  (A ×ˢ A).image (fun p => p.1 * p.2)

def overlap (A : Finset ℝ) : Finset ℝ := sumset A ∩ productset A

def powers (n : ℕ) : Finset ℝ :=
  (range (2 * n)).image (fun i => (2 : ℝ) ^ i)

def shiftedPowers (n : ℕ) : Finset ℝ :=
  (range (2 * n)).image (fun i => 1 + (2 : ℝ) ^ i)

/-- A concrete family consisting entirely of positive integers, viewed in R. -/
def witness (n : ℕ) : Finset ℝ := powers n ∪ shiftedPowers n

def pairValue (n : ℕ) (p : ℕ × ℕ) : ℝ :=
  (2 : ℝ) ^ p.1 + 2 ^ (n + p.2)

def embeddedGrid (n : ℕ) : Finset ℝ :=
  (range n ×ˢ range n).image (pairValue n)

theorem pow_two_injective : Function.Injective (fun i : ℕ => (2 : ℝ) ^ i) :=
  (pow_right_strictMono₀ (by norm_num : (1 : ℝ) < 2)).injective

theorem powers_card (n : ℕ) : (powers n).card = 2 * n := by
  simp only [powers, card_image_of_injective _ pow_two_injective, card_range]

theorem witness_card_lower (n : ℕ) : 2 * n ≤ (witness n).card := by
  rw [← powers_card n]
  exact card_le_card (subset_union_left)

theorem witness_card_upper (n : ℕ) : (witness n).card ≤ 4 * n := by
  have hp := powers_card n
  have hs : (shiftedPowers n).card ≤ 2 * n := by
    exact (card_image_le).trans_eq (card_range _)
  have h := card_union_le (powers n) (shiftedPowers n)
  change (powers n ∪ shiftedPowers n).card ≤ 4 * n
  omega

/-- The leading power separates columns of the grid. -/
theorem pairValue_lt_of_column_lt {n i j k l : ℕ}
    (hi : i < n) (hjl : j < l) :
    pairValue n (i, j) < pairValue n (k, l) := by
  have hsmall : (2 : ℝ) ^ i < 2 ^ (n + j) :=
    pow_lt_pow_right₀ (by norm_num) (by omega)
  have hnext : (2 : ℝ) ^ (n + j + 1) ≤ 2 ^ (n + l) :=
    pow_right_mono₀ (by norm_num) (by omega)
  have hpositive : 0 < (2 : ℝ) ^ k := by positivity
  simp only [pow_succ] at hnext
  simp only [pairValue]
  linarith

theorem pairValue_injective_on (n : ℕ) :
    Set.InjOn (pairValue n) (↑(range n ×ˢ range n) : Set (ℕ × ℕ)) := by
  intro p hp q hq heq
  rcases p with ⟨i, j⟩
  rcases q with ⟨k, l⟩
  simp only [mem_coe, mem_product, mem_range] at hp hq
  have hjl : j = l := by
    rcases lt_trichotomy j l with h | h | h
    · exact False.elim ((ne_of_lt (pairValue_lt_of_column_lt hp.1 h)) heq)
    · exact h
    · exact False.elim ((ne_of_lt (pairValue_lt_of_column_lt hq.1 h)) heq.symm)
  subst l
  have hik : i = k := pow_two_injective (add_right_cancel heq)
  exact Prod.ext hik rfl

theorem embeddedGrid_card (n : ℕ) : (embeddedGrid n).card = n * n := by
  rw [embeddedGrid, card_image_iff.mpr (pairValue_injective_on n)]
  simp

theorem power_mem_witness {n i : ℕ} (hi : i < 2 * n) :
    (2 : ℝ) ^ i ∈ witness n := by
  apply mem_union_left
  exact mem_image.mpr ⟨i, mem_range.mpr hi, rfl⟩

theorem shifted_mem_witness {n i : ℕ} (hi : i < 2 * n) :
    1 + (2 : ℝ) ^ i ∈ witness n := by
  apply mem_union_right
  exact mem_image.mpr ⟨i, mem_range.mpr hi, rfl⟩

theorem embeddedGrid_subset_overlap (n : ℕ) :
    embeddedGrid n ⊆ overlap (witness n) := by
  intro x hx
  obtain ⟨⟨i, j⟩, hij, rfl⟩ := mem_image.mp hx
  simp only [mem_product, mem_range] at hij
  have hi := hij.1
  have hj := hij.2
  have hpi : (2 : ℝ) ^ i ∈ witness n := power_mem_witness (by omega)
  have hpj : (2 : ℝ) ^ (n + j) ∈ witness n := power_mem_witness (by omega)
  have hdiff : n + j - i < 2 * n := by omega
  have hs : 1 + (2 : ℝ) ^ (n + j - i) ∈ witness n :=
    shifted_mem_witness hdiff
  apply mem_inter.mpr
  constructor
  · exact mem_image.mpr ⟨((2 : ℝ) ^ i, 2 ^ (n + j)),
      mem_product.mpr ⟨hpi, hpj⟩, rfl⟩
  · apply mem_image.mpr
    refine ⟨((2 : ℝ) ^ i, 1 + 2 ^ (n + j - i)),
      mem_product.mpr ⟨hpi, hs⟩, ?_⟩
    change (2 : ℝ) ^ i * (1 + 2 ^ (n + j - i)) = 2 ^ i + 2 ^ (n + j)
    rw [mul_add, mul_one, ← pow_add]
    congr 2
    omega

theorem overlap_card_lower (n : ℕ) : n * n ≤ (overlap (witness n)).card := by
  rw [← embeddedGrid_card n]
  exact card_le_card (embeddedGrid_subset_overlap n)

theorem witness_positive_integer {n : ℕ} {x : ℝ} (hx : x ∈ witness n) :
    ∃ k : ℕ, 0 < k ∧ x = (k : ℝ) := by
  rcases mem_union.mp hx with hp | hs
  · obtain ⟨i, _, rfl⟩ := mem_image.mp hp
    refine ⟨2 ^ i, by positivity, ?_⟩
    norm_cast
  · obtain ⟨i, _, rfl⟩ := mem_image.mp hs
    refine ⟨1 + 2 ^ i, by positivity, ?_⟩
    norm_cast

/-- A squared formulation excludes even a uniform O(|A|^(3/2)) bound. -/
theorem arbitrarily_large_super_three_halves (C N : ℕ) :
    ∃ A : Finset ℝ, N ≤ A.card ∧ C * A.card ^ 3 < (overlap A).card ^ 2 := by
  let n := N + 64 * C + 1
  have hn : 0 < n := by dsimp [n]; omega
  have hnC : 64 * C < n := by dsimp [n]; omega
  have hlower := witness_card_lower n
  have hupper := witness_card_upper n
  have hover := overlap_card_lower n
  have hNn : N ≤ n := by dsimp [n]; omega
  refine ⟨witness n, by omega, ?_⟩
  have hgrowth : C * (4 * n) ^ 3 < (n * n) ^ 2 := by
    have h := Nat.mul_lt_mul_of_pos_right hnC (pow_pos hn 3)
    nlinarith only [h]
  exact (Nat.mul_le_mul_left C (Nat.pow_le_pow_left hupper 3)).trans_lt
    (hgrowth.trans_le (Nat.pow_le_pow_left hover 2))

/-- The usual uniform interpretation of |A|^(1+o(1)) in the supremum sense. -/
def SupremumNearLinearBound : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ A : Finset ℝ, N ≤ A.card →
    ((overlap A).card : ℝ) ≤ (A.card : ℝ) ^ (1 + ε)

theorem three_halves_square (x : ℝ) (hx : 0 ≤ x) :
    (x ^ ((3 : ℝ) / 2)) ^ 2 = x ^ 3 := by
  rw [← Real.rpow_mul_natCast hx]
  convert Real.rpow_natCast x 3 using 1
  norm_num

/-- Disproof of the conjecture's asymptotic assertion for actual finite real sets. -/
theorem conjecture40_false : ¬ SupremumNearLinearBound := by
  intro h
  obtain ⟨N, hN⟩ := h ((1 : ℝ) / 2) (by norm_num)
  obtain ⟨A, hsize, hlarge⟩ := arbitrarily_large_super_three_halves 1 N
  have hbound := hN A hsize
  have hsquare := mul_self_le_mul_self (Nat.cast_nonneg (overlap A).card) hbound
  have hidentity : (1 : ℝ) + 1 / 2 = 3 / 2 := by norm_num
  rw [hidentity, ← sq, ← sq, three_halves_square _ (Nat.cast_nonneg _)] at hsquare
  have hcast : (A.card : ℝ) ^ 3 < ((overlap A).card : ℝ) ^ 2 := by
    simp only [one_mul] at hlarge
    exact_mod_cast hlarge
  exact (not_lt_of_ge hsquare) hcast

#print axioms powers_card
#print axioms witness_card_lower
#print axioms witness_card_upper
#print axioms pairValue_injective_on
#print axioms embeddedGrid_subset_overlap
#print axioms overlap_card_lower
#print axioms witness_positive_integer
#print axioms arbitrarily_large_super_three_halves
#print axioms conjecture40_false

end
end Conjecture40
