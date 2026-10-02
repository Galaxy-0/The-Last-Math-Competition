import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
open Filter
open scoped Topology
namespace TLMC793
def digitSum (q : ℕ) : ℕ := (Nat.digits 3 q).sum
theorem even_digit_sum_iff (q : ℕ) (hq : q.Prime) : digitSum q % 2 = 0 ↔ q = 2 := by
  have hm := Nat.modEq_digits_sum 2 3 (by decide) q
  change q % 2 = digitSum q % 2 at hm
  rw [← hm]
  constructor
  · intro h; rcases hq.eq_two_or_odd with hq | hq
    · exact hq
    · omega
  · rintro rfl; decide
theorem even_index_iff (n : ℕ) : digitSum (Nat.nth Nat.Prime n) % 2 = 0 ↔ n = 0 := by
  rw [even_digit_sum_iff _ (Nat.prime_nth_prime n)]
  constructor
  · intro h
    apply (Nat.nth_strictMono Nat.infinite_setOfPred_prime).injective
    simpa only [Nat.nth_prime_zero_eq_two] using h
  · rintro rfl; exact Nat.nth_prime_zero_eq_two

noncomputable def evenCount (N : ℕ) : ℕ := ((Finset.range N).filter
  (fun n => digitSum (Nat.nth Nat.Prime n) % 2 = 0)).card
theorem count_at_most_one (N : ℕ) : evenCount N ≤ 1 := by
  unfold evenCount
  have hsub : (Finset.range N).filter (fun n => digitSum (Nat.nth Nat.Prime n) % 2 = 0) ⊆ {0} := by
    intro n hn
    simp only [Finset.mem_filter] at hn
    simpa only [Finset.mem_singleton] using (even_index_iff n).mp hn.2
  simpa using Finset.card_mono hsub
noncomputable def frequency (N : ℕ) : ℝ := (evenCount N : ℝ) / N
theorem zero_limit : Tendsto frequency atTop (𝓝 0) := by
  have hi : Tendsto (fun N : ℕ => 1 / (N : ℝ)) atTop (𝓝 0) := tendsto_one_div_atTop_nhds_zero_nat
  apply squeeze_zero (fun N => by exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    (fun N => by
      exact div_le_div_of_nonneg_right (by exact_mod_cast count_at_most_one N) (Nat.cast_nonneg _)) hi

theorem not_uniform : ¬ Tendsto frequency atTop (𝓝 (1/2 : ℝ)) := by
  intro h
  have := tendsto_nhds_unique zero_limit h
  norm_num at this
#print axioms even_digit_sum_iff
#print axioms zero_limit
#print axioms not_uniform
end TLMC793
