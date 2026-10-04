import Mathlib.Data.Matrix.DoublyStochastic
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! The k = 1 family of actual Johnson graphs has no total-variation cutoff. -/

namespace Conjecture3961

open scoped BigOperators symmDiff
open Filter

abbrev State (n : ℕ) := Fin (n + 5)
abbrev Vertex (n : ℕ) := {s : Finset (State n) // s.card = 1}

def singletonVertex (n : ℕ) (i : State n) : Vertex n := ⟨{i}, by simp⟩

theorem singleton_bijective (n : ℕ) : Function.Bijective (singletonVertex n) := by
  constructor
  · intro i j h
    have hs := congrArg Subtype.val h
    simpa [singletonVertex] using hs
  · intro s
    obtain ⟨i, hi⟩ := Finset.card_eq_one.mp s.property
    refine ⟨i, ?_⟩
    apply Subtype.ext
    exact hi.symm

noncomputable def singletonEquiv (n : ℕ) : State n ≃ Vertex n :=
  Equiv.ofBijective (singletonVertex n) (singleton_bijective n)

/-- The original symmetric-difference definition, on actual singleton subsets. -/
def johnsonGraph (n : ℕ) : SimpleGraph (Vertex n) where
  Adj s t := (s.val ∆ t.val).card = 2
  symm := by intro s t h; simpa [symmDiff_comm] using h
  loopless := by intro s; simp

instance (n : ℕ) : DecidableRel (johnsonGraph n).Adj := fun s t =>
  inferInstanceAs (Decidable ((s.val ∆ t.val).card = 2))

theorem johnson_singleton_adj (n : ℕ) (i j : State n) :
    (johnsonGraph n).Adj (singletonVertex n i) (singletonVertex n j) ↔ i ≠ j := by
  change (({i} : Finset (State n)) ∆ {j}).card = 2 ↔ i ≠ j
  by_cases h : i = j
  · simp [h]
  · simp [symmDiff_def, Finset.sup_eq_union, Finset.sdiff_singleton_eq_erase,
      h, Ne.symm h]

noncomputable def neighbors (n : ℕ) (i : State n) : Finset (State n) := by
  classical
  exact Finset.univ.filter fun j =>
    (johnsonGraph n).Adj (singletonVertex n i) (singletonVertex n j)

theorem neighbors_eq_erase (n : ℕ) (i : State n) :
    neighbors n i = Finset.univ.erase i := by
  classical
  ext j
  simp [neighbors, johnson_singleton_adj, ne_comm]

theorem neighbor_count (n : ℕ) (i : State n) : (neighbors n i).card = n + 4 := by
  rw [neighbors_eq_erase, Finset.card_erase_of_mem (Finset.mem_univ i)]
  simp only [Finset.card_univ, Fintype.card_fin]
  omega

theorem admissible_parameters (n : ℕ) : 1 ≤ (n + 5) / 2 := by omega

noncomputable def size (n : ℕ) : ℝ := (n : ℝ) + 5

theorem size_ge (n : ℕ) : 5 ≤ size n := by
  dsimp [size]
  linarith [Nat.cast_nonneg (α := ℝ) n]

theorem size_pos (n : ℕ) : 0 < size n := lt_of_lt_of_le (by norm_num) (size_ge n)

theorem size_sub_one_pos (n : ℕ) : 0 < size n - 1 := by linarith [size_ge n]

theorem sum_diagonal (n : ℕ) (i : State n) (a b : ℝ) :
    (∑ j : State n, if i = j then a else b) = a + (size n - 1) * b := by
  calc
    (∑ j : State n, if i = j then a else b) =
        ∑ j : State n, ((if i = j then a - b else 0) + b) := by
      apply Finset.sum_congr rfl
      intro j _
      split_ifs <;> ring
    _ = a + (size n - 1) * b := by simp [Finset.sum_add_distrib, size]; ring

/-- The standard half-lazy walk: stay with probability 1/2, otherwise
choose uniformly from the n+4 neighboring singleton subsets. -/
noncomputable def transition (n : ℕ) : Matrix (State n) (State n) ℝ :=
  Matrix.of fun i j => if i = j then 1 / 2 else 1 / (2 * (size n - 1))

theorem transition_from_johnson (n : ℕ) (i j : State n) :
    transition n i j = if i = j then 1 / 2 else
      if (johnsonGraph n).Adj (singletonVertex n i) (singletonVertex n j)
      then 1 / (2 * (size n - 1)) else 0 := by
  classical
  simp only [transition, Matrix.of_apply, johnson_singleton_adj]
  split_ifs <;> simp_all

theorem transition_by_neighbor_count (n : ℕ) (i j : State n) :
    transition n i j = if i = j then 1 / 2
      else 1 / (2 * ((neighbors n i).card : ℝ)) := by
  have hc : ((neighbors n i).card : ℝ) = size n - 1 := by
    rw [neighbor_count]
    simp [size]
    ring
  rw [hc]
  rfl

theorem transition_pos (n : ℕ) (i j : State n) : 0 < transition n i j := by
  dsimp [transition]
  split_ifs
  · norm_num
  · exact div_pos (by norm_num) (mul_pos (by norm_num) (size_sub_one_pos n))

theorem transition_nonneg (n : ℕ) (i j : State n) : 0 ≤ transition n i j := by
  dsimp [transition]
  split_ifs
  · norm_num
  · exact le_of_lt (div_pos (by norm_num) (mul_pos (by norm_num) (size_sub_one_pos n)))

theorem transition_row_sum (n : ℕ) (i : State n) : ∑ j, transition n i j = 1 := by
  change (∑ j : State n, if i = j then (1 : ℝ) / 2 else 1 / (2 * (size n - 1))) = 1
  rw [sum_diagonal]
  field_simp [(size_sub_one_pos n).ne']
  ring

theorem transition_symmetric (n : ℕ) (i j : State n) :
    transition n i j = transition n j i := by simp [transition, eq_comm]

theorem transition_doubly_stochastic (n : ℕ) :
    transition n ∈ doublyStochastic ℝ (State n) := by
  rw [mem_doublyStochastic_iff_sum]
  refine ⟨transition_nonneg n, transition_row_sum n, ?_⟩
  intro j
  simpa only [transition_symmetric n j] using transition_row_sum n j

theorem powers_doubly_stochastic (n t : ℕ) :
    transition n ^ t ∈ doublyStochastic ℝ (State n) :=
  (doublyStochastic ℝ (State n)).pow_mem (transition_doubly_stochastic n) t

noncomputable def uniform (n : ℕ) (_ : State n) : ℝ := 1 / size n

theorem uniform_nonneg (n : ℕ) (i : State n) : 0 ≤ uniform n i := by
  exact le_of_lt (div_pos (by norm_num) (size_pos n))

theorem uniform_sum (n : ℕ) : ∑ i : State n, uniform n i = 1 := by
  simp [uniform, size, Nat.cast_add]
  field_simp

theorem uniform_stationary (n : ℕ) (j : State n) :
    (∑ i : State n, uniform n i * transition n i j) = uniform n j := by
  simp only [uniform, ← Finset.mul_sum]
  rw [sum_col_of_mem_doublyStochastic (transition_doubly_stochastic n)]
  ring

noncomputable def U (n : ℕ) : Matrix (State n) (State n) ℝ :=
  Matrix.of fun _ _ => 1 / size n

theorem U_idempotent (n : ℕ) : U n * U n = U n := by
  ext i j
  simp [U, Matrix.mul_apply, size]
  field_simp

noncomputable def q (n : ℕ) : ℝ := (size n - 2) / (2 * (size n - 1))

theorem q_nonneg (n : ℕ) : 0 ≤ q n := by
  apply div_nonneg
  · linarith [size_ge n]
  · exact (mul_pos (by norm_num) (size_sub_one_pos n)).le

theorem q_lt_one (n : ℕ) : q n < 1 := by
  apply (div_lt_one (mul_pos (by norm_num) (size_sub_one_pos n))).2
  linarith [size_ge n]

theorem transition_decomposition (n : ℕ) :
    transition n = q n • (1 : Matrix (State n) (State n) ℝ) + (1 - q n) • U n := by
  ext i j
  simp only [transition, Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply,
    Matrix.one_apply, U, smul_eq_mul, q]
  split_ifs <;> field_simp [(size_pos n).ne', (size_sub_one_pos n).ne'] <;> ring

theorem powers_decomposition (n t : ℕ) :
    transition n ^ t = q n ^ t • (1 : Matrix (State n) (State n) ℝ) +
      (1 - q n ^ t) • U n := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [pow_succ, ih, transition_decomposition]
    simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one, U_idempotent, smul_smul]
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, pow_succ]
    ring

/-- Exact finite-space total variation, applied to the actual t-step transition rows. -/
noncomputable def tv (n t : ℕ) (i : State n) : ℝ :=
  (∑ j : State n, |(transition n ^ t) i j - uniform n j|) / 2

theorem tv_exact (n t : ℕ) (i : State n) :
    tv n t i = (size n - 1) / size n * q n ^ t := by
  have ha : 0 ≤ q n ^ t := pow_nonneg (q_nonneg n) _
  have hn : size n ≠ 0 := (size_pos n).ne'
  have hu : 0 ≤ 1 - 1 / size n := by
    have : 1 / size n ≤ (1 : ℝ) := (div_le_one (size_pos n)).2 (by linarith [size_ge n])
    linarith
  have hentry (j : State n) :
      |(transition n ^ t) i j - uniform n j| =
        if i = j then q n ^ t * (1 - 1 / size n) else q n ^ t / size n := by
    rw [powers_decomposition]
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, U,
      Matrix.of_apply, smul_eq_mul, uniform]
    by_cases hij : i = j
    · simp only [if_pos hij]
      have hid : q n ^ t * 1 + (1 - q n ^ t) * (1 / size n) - 1 / size n =
          q n ^ t * (1 - 1 / size n) := by ring
      rw [hid, abs_of_nonneg (mul_nonneg ha hu)]
    · simp only [if_neg hij]
      have hid : q n ^ t * 0 + (1 - q n ^ t) * (1 / size n) - 1 / size n =
          -(q n ^ t / size n) := by ring
      rw [hid, abs_neg, abs_of_nonneg (div_nonneg ha (size_pos n).le)]
  unfold tv
  simp_rw [hentry]
  rw [sum_diagonal]
  field_simp
  ring

theorem tv_zero_gt_three_quarters (n : ℕ) (i : State n) :
    (3 : ℝ) / 4 < tv n 0 i := by
  rw [tv_exact]
  simp only [pow_zero, mul_one]
  apply (lt_div_iff₀ (size_pos n)).2
  linarith [size_ge n]

theorem tv_one (n : ℕ) (i : State n) :
    tv n 1 i = (size n - 2) / (2 * size n) := by
  rw [tv_exact]
  simp only [pow_one, q]
  field_simp [(size_pos n).ne', (size_sub_one_pos n).ne']
  ring

theorem tv_one_gt_quarter (n : ℕ) (i : State n) : (1 : ℝ) / 4 < tv n 1 i := by
  rw [tv_one]
  apply (lt_div_iff₀ (mul_pos (by norm_num) (size_pos n))).2
  linarith [size_ge n]

theorem tv_one_le_three_quarters (n : ℕ) (i : State n) :
    tv n 1 i ≤ (3 : ℝ) / 4 := by
  rw [tv_one]
  apply (div_le_iff₀ (mul_pos (by norm_num) (size_pos n))).2
  linarith [size_ge n]

theorem tv_two (n : ℕ) (i : State n) :
    tv n 2 i = (size n - 2) ^ 2 / (4 * size n * (size n - 1)) := by
  rw [tv_exact]
  dsimp [q]
  field_simp [(size_pos n).ne', (size_sub_one_pos n).ne']
  ring

theorem tv_two_le_quarter (n : ℕ) (i : State n) : tv n 2 i ≤ (1 : ℝ) / 4 := by
  rw [tv_two]
  apply (div_le_iff₀ (mul_pos (mul_pos (by norm_num) (size_pos n))
    (size_sub_one_pos n))).2
  nlinarith [size_ge n]

theorem tv_tendsto_zero (n : ℕ) (i : State n) :
    Tendsto (fun t : ℕ => tv n t i) atTop (nhds 0) := by
  simp_rw [tv_exact]
  simpa only [mul_zero] using
    (tendsto_pow_atTop_nhds_zero_of_lt_one (q_nonneg n) (q_lt_one n)).const_mul
      ((size n - 1) / size n)

/-- All starting states must be within epsilon in total variation. -/
def MixesAt (n t : ℕ) (ε : ℝ) : Prop := ∀ i : State n, tv n t i ≤ ε

theorem exists_mixing_time (n : ℕ) {ε : ℝ} (hε : 0 < ε) : ∃ t, MixesAt n t ε := by
  let i : State n := ⟨0, by omega⟩
  have hlt : ∀ᶠ t in atTop, tv n t i < ε :=
    (tendsto_order.1 (tv_tendsto_zero n i)).2 ε hε
  obtain ⟨t, ht⟩ := hlt.exists
  refine ⟨t, fun j => ?_⟩
  rw [tv_exact] at ht ⊢
  exact ht.le

/-- The least admissible nonnegative integer time. Nonemptiness is proved for
both tolerances used below, so the empty-set infimum convention is irrelevant. -/
noncomputable def mixingTime (n : ℕ) (ε : ℝ) : ℕ := sInf {t | MixesAt n t ε}

theorem mixingTime_quarter (n : ℕ) : mixingTime n (1 / 4) = 2 := by
  apply IsLeast.csInf_eq
  refine ⟨tv_two_le_quarter n, ?_⟩
  intro t ht
  by_contra h
  have htlt : t < 2 := Nat.lt_of_not_ge h
  have ht01 : t = 0 ∨ t = 1 := by omega
  rcases ht01 with rfl | rfl
  · have hb := ht ⟨0, by omega⟩
    have ha := tv_zero_gt_three_quarters n ⟨0, by omega⟩
    linarith
  · exact (not_le_of_gt (tv_one_gt_quarter n ⟨0, by omega⟩)) (ht ⟨0, by omega⟩)

theorem mixingTime_three_quarters (n : ℕ) : mixingTime n (3 / 4) = 1 := by
  apply IsLeast.csInf_eq
  refine ⟨tv_one_le_three_quarters n, ?_⟩
  intro t ht
  by_contra h
  have ht0 : t = 0 := by omega
  subst t
  exact (not_le_of_gt (tv_zero_gt_three_quarters n ⟨0, by omega⟩)) (ht ⟨0, by omega⟩)

/-- The standard total-variation cutoff ratio criterion for this graph family. -/
def HasTotalVariationCutoff : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 1 / 2 →
    Tendsto (fun n : ℕ => (mixingTime n ε : ℝ) / (mixingTime n (1 - ε) : ℝ))
      atTop (nhds 1)

theorem mixing_ratio (n : ℕ) :
    (mixingTime n (1 / 4) : ℝ) / (mixingTime n (3 / 4) : ℝ) = 2 := by
  rw [mixingTime_quarter, mixingTime_three_quarters]
  norm_num

theorem no_total_variation_cutoff : ¬ HasTotalVariationCutoff := by
  intro h
  have h1 := h (1 / 4) (by norm_num) (by norm_num)
  have hsub : (1 : ℝ) - 1 / 4 = 3 / 4 := by norm_num
  simp_rw [hsub, mixing_ratio] at h1
  have heq : (2 : ℝ) = 1 := tendsto_nhds_unique tendsto_const_nhds h1
  norm_num at heq

#print axioms singleton_bijective
#print axioms johnson_singleton_adj
#print axioms neighbor_count
#print axioms transition_from_johnson
#print axioms transition_by_neighbor_count
#print axioms transition_pos
#print axioms transition_doubly_stochastic
#print axioms powers_doubly_stochastic
#print axioms uniform_stationary
#print axioms powers_decomposition
#print axioms tv_exact
#print axioms tv_tendsto_zero
#print axioms exists_mixing_time
#print axioms mixingTime_quarter
#print axioms mixingTime_three_quarters
#print axioms no_total_variation_cutoff

end Conjecture3961
