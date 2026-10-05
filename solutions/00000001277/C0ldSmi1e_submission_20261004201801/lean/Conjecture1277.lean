import Conjecture1277.Markov
import Conjecture1277.Counterexample

namespace Conjecture1277

/-- The fixed admissibility matrix allows exactly the six off-diagonal transitions. -/
def Admissible (K : Fin 3 → PMF (Fin 3)) : Prop := ∀ i, K i i = 0

/-- Maximality compares actual entropy-rate limits for all initial laws and admissible kernels. -/
def MaximizesEntropyRate (π : PMF (Fin 3)) (K : Fin 3 → PMF (Fin 3)) (h : ℝ) : Prop :=
  Admissible K ∧ HasEntropyRate π K h ∧
    ∀ (q : PMF (Fin 3)) (L : Fin 3 → PMF (Fin 3)) (r : ℝ),
      Admissible L → HasEntropyRate q L r → r ≤ h

theorem admissible_block_entropy_bound (π : PMF (Fin 3)) (K : Fin 3 → PMF (Fin 3))
    (hK : Admissible K) (n : ℕ) :
    entropy (blockLaw π K n) ≤ entropy π + (n : ℝ) * Real.log 2 :=
  block_entropy_le π K (Real.log 2) (fun i => entropy_le_log_two_of_zero (K i) i (hK i)) n

theorem admissible_entropyRate_bound (π : PMF (Fin 3)) (K : Fin 3 → PMF (Fin 3))
    (hK : Admissible K) (r : ℝ) (hr : HasEntropyRate π K r) : r ≤ Real.log 2 :=
  entropyRate_le π K (Real.log 2) (fun i => entropy_le_log_two_of_zero (K i) i (hK i)) hr

theorem initial_entropy : entropy initial = Real.log 3 := by
  rw [entropy_fin_three]
  simp [Real.negMulLog, Real.log_inv]
  ring

theorem witness_block_entropy (n : ℕ) :
    entropy (blockLaw initial transition n) = Real.log 3 + (n : ℝ) * Real.log 2 := by
  rw [block_entropy_of_constant_rows initial transition (Real.log 2) transition_entropy,
    initial_entropy]

theorem witness_entropyRate : HasEntropyRate initial transition (Real.log 2) :=
  hasEntropyRate_of_constant_rows initial transition (Real.log 2) transition_entropy

theorem witness_maximizes : MaximizesEntropyRate initial transition (Real.log 2) := by
  refine ⟨transition_self, witness_entropyRate, ?_⟩
  intro q L r hL hr
  exact admissible_entropyRate_bound q L hL r hr

theorem partialPermutation_block_entropy (π : PMF (Fin 3)) (K : Fin 3 → PMF (Fin 3))
    (hK : PartialPermutationSupport K) (n : ℕ) :
    entropy (blockLaw π K n) = entropy π := by
  simpa using block_entropy_of_constant_rows π K 0 (partialPermutation_row_entropy_zero K hK) n

theorem partialPermutation_entropyRate (π : PMF (Fin 3)) (K : Fin 3 → PMF (Fin 3))
    (hK : PartialPermutationSupport K) : HasEntropyRate π K 0 :=
  hasEntropyRate_of_constant_rows π K 0 (partialPermutation_row_entropy_zero K hK)

theorem no_partialPermutation_maximizer (π : PMF (Fin 3)) (K : Fin 3 → PMF (Fin 3))
    (h : ℝ) (hm : MaximizesEntropyRate π K h) : ¬ PartialPermutationSupport K := by
  intro hK
  have hz : h = 0 := entropyRate_unique π K hm.2.1 (partialPermutation_entropyRate π K hK)
  have hmax := hm.2.2 initial transition (Real.log 2) transition_self witness_entropyRate
  have hp : 0 < Real.log 2 := Real.log_pos (by norm_num)
  linarith

/-- The support clause specialized to a particular valid first-order admissibility matrix. -/
def SupportConjecture : Prop :=
  ∀ (π : PMF (Fin 3)) (K : Fin 3 → PMF (Fin 3)) (h : ℝ),
    MaximizesEntropyRate π K h → PartialPermutationSupport K

theorem explicit_counterexample :
    Stationary initial transition ∧
    MaximizesEntropyRate initial transition (Real.log 2) ∧
    ¬ PartialPermutationSupport transition ∧
    joint initial transition ≠ joint initial (fun _ => initial) :=
  ⟨initial_stationary, witness_maximizes, transition_not_partialPermutation,
    stationary_pair_not_independent⟩

/-- This necessary instance of the conjecture's support assertion is false. -/
theorem conjecture_1277 : ¬ SupportConjecture := by
  intro h
  exact transition_not_partialPermutation (h initial transition (Real.log 2) witness_maximizes)

end Conjecture1277
