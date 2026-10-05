import Conjecture1277.Entropy
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Tactic

namespace Conjecture1277

open scoped ENNReal BigOperators

noncomputable section

/-- The stationary initial law on all three states. -/
def initial : PMF (Fin 3) := PMF.uniformOfFintype (Fin 3)

/-- Self transitions are forbidden; the other two successors are equally likely. -/
def transition (i : Fin 3) : PMF (Fin 3) :=
  PMF.ofFintype (fun j => if j = i then 0 else (1 / 2 : ℝ≥0∞)) (by
    fin_cases i <;> simp +decide [Fin.sum_univ_succ, ENNReal.inv_two_add_inv_two]
    exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num))

@[simp] theorem initial_apply (i : Fin 3) : initial i = (1 / 3 : ℝ≥0∞) := by
  norm_num [initial, PMF.uniformOfFintype_apply]

@[simp] theorem transition_apply (i j : Fin 3) :
    transition i j = if j = i then 0 else (1 / 2 : ℝ≥0∞) := by
  simp [transition, PMF.ofFintype_apply]

@[simp] theorem transition_self (i : Fin 3) : transition i i = 0 := by simp

theorem transition_of_ne {i j : Fin 3} (h : j ≠ i) :
    transition i j = (1 / 2 : ℝ≥0∞) := by simp [h]

theorem transition_pos_of_ne {i j : Fin 3} (h : j ≠ i) : 0 < transition i j := by
  rw [transition_of_ne h]
  norm_num

theorem initial_stationary : initial.bind transition = initial := by
  ext j
  rw [PMF.bind_apply, tsum_fintype]
  fin_cases j <;> simp +decide [Fin.sum_univ_succ, ← mul_add,
    ENNReal.inv_two_add_inv_two]

/-- A partial permutation support has at most one successor and one predecessor per state. -/
def PartialPermutationSupport (K : Fin 3 → PMF (Fin 3)) : Prop :=
  (∀ i j k, 0 < K i j → 0 < K i k → j = k) ∧
  (∀ i j k, 0 < K i j → 0 < K k j → i = k)

theorem transition_not_partialPermutation : ¬ PartialPermutationSupport transition := by
  intro h
  have he := h.1 0 1 2 (transition_pos_of_ne (by decide))
    (transition_pos_of_ne (by decide))
  exact (by decide : (1 : Fin 3) ≠ 2) he

theorem transition_zero_ne_one : transition 0 ≠ transition 1 := by
  intro h
  have he := congrArg (fun p : PMF (Fin 3) => p 0) h
  change transition 0 0 = transition 1 0 at he
  have hp := transition_pos_of_ne (show (0 : Fin 3) ≠ 1 by decide)
  rw [← he, transition_self] at hp
  exact (lt_irrefl 0) hp

theorem transition_not_constant : ¬ ∃ p : PMF (Fin 3), ∀ i, transition i = p := by
  rintro ⟨p, hp⟩
  exact transition_zero_ne_one ((hp 0).trans (hp 1).symm)

@[simp] theorem entropy_pure {α : Type*} [Fintype α] (a : α) :
    entropy (PMF.pure a) = 0 := by
  classical
  simp [entropy, PMF.pure_apply, apply_ite]

theorem entropy_fin_three (p : PMF (Fin 3)) :
    entropy p = Real.negMulLog ((p 0).toReal) + Real.negMulLog ((p 1).toReal) +
      Real.negMulLog ((p 2).toReal) := by
  simp [entropy, Fin.sum_univ_succ, add_assoc]

theorem sum_prob_fin_three (p : PMF (Fin 3)) :
    (p 0).toReal + (p 1).toReal + (p 2).toReal = 1 := by
  simpa [Fin.sum_univ_succ, add_assoc] using sum_prob p

theorem transition_entropy (i : Fin 3) : entropy (transition i) = Real.log 2 := by
  rw [entropy_fin_three]
  fin_cases i <;> simp +decide [Real.negMulLog, Real.log_inv] <;> ring

theorem entropy_le_log_two_of_zero (p : PMF (Fin 3)) (i : Fin 3) (hi : p i = 0) :
    entropy p ≤ Real.log 2 := by
  have hs := sum_prob_fin_three p
  rw [entropy_fin_three]
  fin_cases i
  · change p 0 = 0 at hi
    rw [hi] at hs ⊢
    simp only [ENNReal.toReal_zero, Real.negMulLog_zero, zero_add] at hs ⊢
    have hc : (p 2).toReal = 1 - (p 1).toReal := by linarith
    rw [hc, ← Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
    exact Real.binEntropy_le_log_two
  · change p 1 = 0 at hi
    rw [hi] at hs ⊢
    simp only [ENNReal.toReal_zero, Real.negMulLog_zero, add_zero] at hs ⊢
    have hc : (p 2).toReal = 1 - (p 0).toReal := by linarith
    rw [hc, ← Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
    exact Real.binEntropy_le_log_two
  · change p 2 = 0 at hi
    rw [hi] at hs ⊢
    simp only [ENNReal.toReal_zero, Real.negMulLog_zero, add_zero] at hs ⊢
    have hb : (p 1).toReal = 1 - (p 0).toReal := by linarith
    rw [hb, ← Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
    exact Real.binEntropy_le_log_two

theorem weighted_entropy_le_log_two (p : PMF (Fin 3)) (K : Fin 3 → PMF (Fin 3))
    (hK : ∀ i, K i i = 0) :
    (∑ i, (p i).toReal * entropy (K i)) ≤ Real.log 2 := by
  calc
    _ ≤ ∑ i, (p i).toReal * Real.log 2 := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left (entropy_le_log_two_of_zero (K i) i (hK i))
        ENNReal.toReal_nonneg
    _ = Real.log 2 := by rw [← Finset.sum_mul, sum_prob, one_mul]

theorem initial_transition_entropy :
    (∑ i, (initial i).toReal * entropy (transition i)) = Real.log 2 := by
  simp only [transition_entropy, ← Finset.sum_mul, sum_prob, one_mul]

theorem eq_pure_of_unique_successor (p : PMF (Fin 3))
    (h : ∀ j k, 0 < p j → 0 < p k → j = k) : ∃ j, p = PMF.pure j := by
  classical
  obtain ⟨j, hj⟩ := p.support_nonempty
  have hpj : 0 < p j := (p.apply_pos_iff j).2 hj
  have hs : p.support = {j} := by
    ext k
    constructor
    · intro hk
      exact Set.mem_singleton_iff.mpr (h k j ((p.apply_pos_iff k).2 hk) hpj)
    · intro hk
      simpa using (Set.mem_singleton_iff.mp hk) ▸ hj
  have hjone : p j = 1 := (p.apply_eq_one_iff j).2 hs
  refine ⟨j, ?_⟩
  ext k
  by_cases hk : k = j
  · simp [hk, hjone]
  · have hzero : p k = 0 := by
      apply (p.apply_eq_zero_iff k).2
      simpa [hs] using hk
    simp [PMF.pure_apply, hk, hzero]

theorem partialPermutation_row_entropy_zero (K : Fin 3 → PMF (Fin 3))
    (hK : PartialPermutationSupport K) (i : Fin 3) : entropy (K i) = 0 := by
  obtain ⟨j, hj⟩ := eq_pure_of_unique_successor (K i) (hK.1 i)
  rw [hj, entropy_pure]

theorem partialPermutation_weighted_entropy_zero (p : PMF (Fin 3))
    (K : Fin 3 → PMF (Fin 3)) (hK : PartialPermutationSupport K) :
    (∑ i, (p i).toReal * entropy (K i)) = 0 := by
  simp [partialPermutation_row_entropy_zero K hK]

/-- The actual first two coordinates have a joint law different from independent stationary draws. -/
theorem stationary_pair_not_independent :
    joint initial transition ≠ joint initial (fun _ => initial) := by
  intro h
  have he := congrArg (fun p : PMF (Fin 3 × Fin 3) => p (0, 0)) h
  change joint initial transition (0, 0) = joint initial (fun _ => initial) (0, 0) at he
  rw [joint_apply, joint_apply, transition_self, mul_zero] at he
  have hp : 0 < initial (0 : Fin 3) * initial 0 := by simp
  rw [← he] at hp
  exact (lt_irrefl 0) hp

end

end Conjecture1277
