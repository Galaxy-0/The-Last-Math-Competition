import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace SparseProxCounterexample

noncomputable section

-- Actual scalar ℓ0 penalty: the count of nonzero scalar coordinates.
def sparsePenalty (y : ℝ) : ℝ := if y = 0 then 0 else 1

def objective (x y : ℝ) : ℝ := (y - x)^2 / 2 + sparsePenalty y

def Prox (x y : ℝ) : Prop := ∀ z : ℝ, objective x y ≤ objective x z

def softThreshold (tau x : ℝ) : ℝ :=
  if tau < x then x - tau else if x < -tau then x + tau else 0

theorem penalty_zero : sparsePenalty 0 = 0 := by simp [sparsePenalty]

theorem penalty_nonzero (y : ℝ) (hy : y ≠ 0) : sparsePenalty y = 1 := by
  simp [sparsePenalty, hy]

theorem prox_two : Prox 2 2 := by
  intro z
  by_cases hz : z = 0
  · subst z
    norm_num [objective, sparsePenalty]
  · simp only [objective, penalty_nonzero z hz]
    norm_num [sparsePenalty]
    nlinarith [sq_nonneg (z - 2)]

theorem prox_two_iff (y : ℝ) : Prox 2 y ↔ y = 2 := by
  constructor
  · intro h
    have hp := h 2
    by_cases hy : y = 0
    · subst y
      norm_num [objective, sparsePenalty] at hp
    · simp only [objective, penalty_nonzero y hy] at hp
      norm_num [sparsePenalty] at hp
      nlinarith [sq_nonneg (y - 2)]
  · intro hy
    subst y
    exact prox_two

theorem prox_one : Prox 1 0 := by
  intro z
  by_cases hz : z = 0
  · subst z
    exact le_rfl
  · simp only [objective, penalty_nonzero z hz]
    norm_num [sparsePenalty]
    nlinarith [sq_nonneg (z - 1)]

theorem prox_one_iff (y : ℝ) : Prox 1 y ↔ y = 0 := by
  constructor
  · intro h
    have hp := h 0
    by_cases hy : y = 0
    · exact hy
    · simp only [objective, penalty_nonzero y hy] at hp
      norm_num [sparsePenalty] at hp
      nlinarith [sq_nonneg (y - 1)]
  · intro hy
    subst y
    exact prox_one

theorem soft_at_two_forces_zero (tau : ℝ) (htau : 0 ≤ tau)
    (h : Prox 2 (softThreshold tau 2)) : tau = 0 := by
  have heq := (prox_two_iff _).mp h
  unfold softThreshold at heq
  split_ifs at heq with hfirst hsecond
  · linarith
  · linarith
  · norm_num at heq

theorem soft_zero_at_one : softThreshold 0 1 = 1 := by
  norm_num [softThreshold]

theorem conjecture_8855_false :
    ¬ (∃ tau : ℝ, 0 ≤ tau ∧ ∀ x : ℝ, Prox x (softThreshold tau x)) := by
  rintro ⟨tau, htau, hall⟩
  have hz := soft_at_two_forces_zero tau htau (hall 2)
  subst tau
  have h := (prox_one_iff _).mp (hall 1)
  rw [soft_zero_at_one] at h
  norm_num at h

theorem unit_threshold_failure : ¬ Prox 2 (softThreshold 1 2) := by
  rw [prox_two_iff]
  norm_num [softThreshold]

end
end SparseProxCounterexample

#print axioms SparseProxCounterexample.prox_two_iff
#print axioms SparseProxCounterexample.prox_one_iff
#print axioms SparseProxCounterexample.conjecture_8855_false
