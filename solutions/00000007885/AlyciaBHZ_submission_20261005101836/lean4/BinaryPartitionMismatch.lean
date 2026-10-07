/-
# Disproof of TLMC conjecture 00000007885

Conjecture (verbatim):
"Definition: The higher iterates of topological Hochschild homology THH^{(n)}(A) = THH(THH^{(n-1)}(A)), of homotopy-limit type A^{S^n}. Conjecture: For the sphere spectrum S, the grading of the p-completed homotopy groups of THH^{(n)}(S) forms a skew-symmetric tridiagonal system in the three coordinates (weight, stem, n); its graded count polynomial P_n(t) satisfies the self-similar doubling law P_{n+1} = P_n(1+t^{2^n}), so the dimension generating function of the homology of iterated THH is the infinite product over k of (1+t^{2^k}), matching the binary partition numbers. (iterated THH binary partition grading)"

Reading formalized: the final explicit combinatorial assertion identifies the
coefficients of the product over k >= 0 with the number of unordered partitions
into powers of two, allowing repeated parts. We define genuine finite products
in Polynomial Nat, prove their full coefficient formula, and define the infinite
product by coefficientwise stabilization. Binary partitions are a filter of
Mathlib's Nat.Partition. Their count at 2 is 2, whereas the product coefficient
is 1. No topological assertion is required for this refutation of a claimed
consequence. Partitions into DISTINCT powers of two are a different reading;
for that reading the stated product is correct, as explained in the report.
-/
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Tactic

/-! Module documentation: see the opening block for the verbatim conjecture and
reading. This module disproves its final combinatorial matching clause. -/

namespace BinaryPartitionMismatch

open Polynomial
open scoped BigOperators

/-- The actual truncated product, with exactly the factors indexed by k < K. -/
noncomputable def truncatedProduct (K : ℕ) : Polynomial ℕ :=
  ∏ k ∈ Finset.range K, (1 + X ^ (2 ^ k))

/-- Every coefficient, including the zero coefficients beyond the degree. -/
theorem truncatedProduct_coeff (K n : ℕ) :
    (truncatedProduct K).coeff n = if n < 2 ^ K then 1 else 0 := by
  induction K generalizing n with
  | zero =>
      simp [truncatedProduct, Polynomial.coeff_one]
  | succ K ih =>
      rw [truncatedProduct, Finset.prod_range_succ]
      change (truncatedProduct K * (1 + X ^ (2 ^ K))).coeff n = _
      rw [mul_add, mul_one, coeff_add, coeff_mul_X_pow', ih]
      simp only [ih, pow_succ]
      split_ifs <;> omega

/-- The product is precisely the finite geometric sum. -/
theorem truncatedProduct_eq_sum (K : ℕ) :
    truncatedProduct K = ∑ n ∈ Finset.range (2 ^ K), (X : Polynomial ℕ) ^ n := by
  ext n
  rw [truncatedProduct_coeff]
  simp [Polynomial.finsetSum_coeff, Polynomial.coeff_X_pow]

theorem truncatedProduct_coeff_one {K n : ℕ} (h : n < 2 ^ K) :
    (truncatedProduct K).coeff n = 1 := by
  rw [truncatedProduct_coeff, if_pos h]

/-- Choose a finite truncation already long enough to determine degree n. -/
noncomputable def infiniteProductCoeff (n : ℕ) : ℕ := (truncatedProduct (n + 1)).coeff n

lemma index_lt_two_pow (n : ℕ) : n < 2 ^ (n + 1) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [pow_succ]
      have hp : 0 < 2 ^ (n + 1) := by positivity
      omega

theorem infiniteProductCoeff_eq_one (n : ℕ) : infiniteProductCoeff n = 1 :=
  truncatedProduct_coeff_one (index_lt_two_pow n)

/-- This makes the coefficientwise-limit definition independent of truncation. -/
theorem coefficient_stabilization {K n : ℕ} (h : n < 2 ^ K) :
    (truncatedProduct K).coeff n = infiniteProductCoeff n := by
  rw [truncatedProduct_coeff_one h, infiniteProductCoeff_eq_one]

/-- An explicit eventual-stability statement for every fixed degree. -/
theorem coefficient_eventually_stable (n : ℕ) :
    ∀ K, n + 1 ≤ K → (truncatedProduct K).coeff n = infiniteProductCoeff n := by
  intro K hK
  apply coefficient_stabilization
  exact (index_lt_two_pow n).trans_le (Nat.pow_le_pow_right (by decide) hK)

/-- Powers of two include 1 = 2^0, and allow no zero part. -/
def IsPowerOfTwo (m : ℕ) : Prop := ∃ k : ℕ, m = 2 ^ k

/-- Ordinary binary partitions: unordered, positive, repeated parts allowed. -/
noncomputable def binaryPartitions (n : ℕ) : Finset (Nat.Partition n) := by
  classical
  exact Finset.univ.filter fun p => ∀ m ∈ p.parts, IsPowerOfTwo m

noncomputable def binaryPartitionNumber (n : ℕ) : ℕ := (binaryPartitions n).card

/-- The partition {2}. -/
def singleTwo : Nat.Partition 2 where
  parts := {2}
  parts_pos := by simp
  parts_sum := by simp

/-- The partition {1,1}; repetition is essential to the counterexample. -/
def twoOnes : Nat.Partition 2 where
  parts := {1, 1}
  parts_pos := by simp
  parts_sum := by simp

lemma singleTwo_ne_twoOnes : singleTwo ≠ twoOnes := by
  intro h
  have hc := congrArg (fun p : Nat.Partition 2 => p.parts.card) h
  norm_num [singleTwo, twoOnes] at hc

/-- Exhaustive enumeration of all partitions of 2, not just two witnesses. -/
theorem partition_two_classification (p : Nat.Partition 2) :
    p = singleTwo ∨ p = twoOnes := by
  by_cases htwo : 2 ∈ p.parts
  · left
    have hs : 2 + (p.parts.erase 2).sum = 2 := by
      simpa [p.parts_sum] using congrArg Multiset.sum (Multiset.cons_erase htwo)
    have he : p.parts.erase 2 = 0 := by
      have hz : (p.parts.erase 2).sum = 0 := by omega
      apply Multiset.eq_zero_of_forall_notMem
      intro m hm
      have hm0 := Multiset.sum_eq_zero_iff.mp hz m hm
      have hp := p.parts_pos (Multiset.mem_of_mem_erase hm)
      omega
    apply Nat.Partition.ext
    simpa [singleTwo, he] using (Multiset.cons_erase htwo).symm
  · right
    have hr : p.parts = Multiset.replicate p.parts.card 1 :=
      Multiset.eq_replicate_card.mpr fun m hm => by
        have hlo := p.parts_pos hm
        have hhi := p.le_of_mem_parts hm
        have hn : m ≠ 2 := by intro he; subst m; exact htwo hm
        omega
    have hc : p.parts.card = 2 := by
      have hs := p.parts_sum
      rw [hr] at hs
      simpa using hs
    apply Nat.Partition.ext
    simpa [hc, twoOnes, Multiset.replicate_succ] using hr

lemma isPowerOfTwo_one : IsPowerOfTwo 1 := ⟨0, rfl⟩
lemma isPowerOfTwo_two : IsPowerOfTwo 2 := ⟨1, rfl⟩

theorem binaryPartitions_two : binaryPartitions 2 = {singleTwo, twoOnes} := by
  classical
  ext p
  simp only [binaryPartitions, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro _
    exact partition_two_classification p
  · rintro (rfl | rfl)
    · simpa [singleTwo] using isPowerOfTwo_two
    · simpa [twoOnes] using isPowerOfTwo_one

/-- The conventional binary partition count at 2 is exactly 2. -/
theorem binaryPartitionNumber_two : binaryPartitionNumber 2 = 2 := by
  classical
  rw [binaryPartitionNumber, binaryPartitions_two]
  simp [singleTwo_ne_twoOnes]

/-- Concrete mismatch in every sufficiently long finite truncation. -/
theorem finite_counterexample (K : ℕ) (hK : 2 ≤ K) :
    (truncatedProduct K).coeff 2 = 1 ∧ binaryPartitionNumber 2 = 2 ∧
      (truncatedProduct K).coeff 2 ≠ binaryPartitionNumber 2 := by
  have hpow : 2 < 2 ^ K :=
    lt_of_lt_of_le (by norm_num : 2 < 2 ^ 2)
      (Nat.pow_le_pow_right (by decide) hK)
  rw [truncatedProduct_coeff_one hpow, binaryPartitionNumber_two]
  decide

/-- The final matching clause of the conjecture, with ordinary binary partitions. -/
def MatchingClause : Prop := ∀ n : ℕ, infiniteProductCoeff n = binaryPartitionNumber n

/-- Main refutation: the stable product coefficients are not binary partition numbers. -/
theorem conjecture_00000007885_false : ¬ MatchingClause := by
  intro h
  have hc := h 2
  rw [infiniteProductCoeff_eq_one, binaryPartitionNumber_two] at hc
  norm_num at hc

/-- The same assertion as inequality of coefficient sequences. -/
theorem coefficient_sequences_ne : infiniteProductCoeff ≠ binaryPartitionNumber := by
  intro h
  exact conjecture_00000007885_false (congrFun h)

end BinaryPartitionMismatch

#print axioms BinaryPartitionMismatch.truncatedProduct_coeff
#print axioms BinaryPartitionMismatch.truncatedProduct_eq_sum
#print axioms BinaryPartitionMismatch.coefficient_eventually_stable
#print axioms BinaryPartitionMismatch.binaryPartitionNumber_two
#print axioms BinaryPartitionMismatch.finite_counterexample
#print axioms BinaryPartitionMismatch.conjecture_00000007885_false
#print axioms BinaryPartitionMismatch.coefficient_sequences_ne
