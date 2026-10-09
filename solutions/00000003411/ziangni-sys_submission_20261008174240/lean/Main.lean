import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic

open scoped NNReal
namespace MarkovEntropy

abbrev Transition := Fin 2 → Fin 2 → ℝ
def distribution (p : ℝ) (j : Fin 2) : ℝ := if j = 0 then p else 1 - p
def transition (p : ℝ) : Transition := fun _ j => distribution p j

def RowStochastic (P : Transition) : Prop :=
  (∀ i j, 0 ≤ P i j) ∧ ∀ i, ∑ j, P i j = 1

def Stationary (π : Fin 2 → ℝ) (P : Transition) : Prop :=
  (∀ i, 0 ≤ π i) ∧ (∑ i, π i = 1) ∧ ∀ j, ∑ i, π i * P i j = π j

/-- The usual entropy-rate formula for a stationary finite-state Markov chain. -/
noncomputable def entropyRate (π : Fin 2 → ℝ) (P : Transition) : ℝ :=
  - ∑ i, π i * ∑ j, P i j * Real.log (P i j)

noncomputable def binaryEntropy (p : ℝ) : ℝ :=
  -p * Real.log p - (1-p) * Real.log (1-p)

theorem valid_chain {p : ℝ} (hp : p ∈ Set.Icc 0 1) :
    RowStochastic (transition p) ∧ Stationary (distribution p) (transition p) := by
  rcases hp with ⟨hp0, hp1⟩
  constructor
  · constructor
    · intro i j
      fin_cases j <;> simp [transition, distribution] <;> linarith
    · intro i
      simp [transition, distribution, Fin.sum_univ_two]
  · constructor
    · intro i
      fin_cases i <;> simp [distribution] <;> linarith
    · constructor
      · simp [distribution, Fin.sum_univ_two]
      · intro j
        fin_cases j <;> simp [distribution, transition, Fin.sum_univ_two] <;> ring

theorem entropy_formula (p : ℝ) :
    entropyRate (distribution p) (transition p) = binaryEntropy p := by
  simp [entropyRate, binaryEntropy, transition, distribution, Fin.sum_univ_two]
  ring

/-- The standard maximum-entry distance of the transition matrices is |p-q|. -/
theorem transition_distance (p q : ℝ) : dist (transition p) (transition q) = |p-q| := by
  have hdist : ∀ i j, dist (transition p i j) (transition q i j) = |p-q| := by
    intro i j
    fin_cases j <;> simp [transition, distribution, Real.dist_eq]
    rw [show 1-p+q-1 = -(p-q) by ring, abs_neg]
  apply le_antisymm
  · apply (dist_pi_le_iff (abs_nonneg _)).2
    intro i
    apply (dist_pi_le_iff (abs_nonneg _)).2
    intro j
    exact (hdist i j).le
  · have h := (dist_le_pi_dist (transition p 0) (transition q 0) 0).trans
      (dist_le_pi_dist (transition p) (transition q) 0)
    simpa only [hdist] using h

theorem entropy_zero : binaryEntropy 0 = 0 := by simp [binaryEntropy]

/-- Explicitly, every proposed Lipschitz constant is violated by a valid chain. -/
theorem counterexample (C : ℝ) (hC : 0 ≤ C) :
    ∃ p ∈ Set.Icc (0 : ℝ) 1,
      RowStochastic (transition p) ∧ Stationary (distribution p) (transition p) ∧
      C * dist (transition p) (transition 0) <
        |entropyRate (distribution p) (transition p) -
          entropyRate (distribution 0) (transition 0)| := by
  let p := Real.exp (-(C+1))
  have hp0 : 0 < p := Real.exp_pos _
  have hp1 : p < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hlog : Real.log p = -(C+1) := Real.log_exp _
  have hremain : 0 ≤ -(1-p) * Real.log (1-p) := by
    apply mul_nonneg_of_nonpos_of_nonpos
    · linarith
    · apply Real.log_nonpos <;> linarith
  have hlower : C * p < binaryEntropy p := by
    unfold binaryEntropy
    rw [hlog]
    nlinarith
  have hpos : 0 ≤ binaryEntropy p := le_trans (mul_nonneg hC hp0.le) hlower.le
  obtain ⟨hrow, hstat⟩ := valid_chain ⟨hp0.le, hp1.le⟩
  refine ⟨p, ⟨hp0.le, hp1.le⟩, hrow, hstat, ?_⟩
  rw [transition_distance, entropy_formula, entropy_formula, entropy_zero, sub_zero,
    sub_zero, abs_of_pos hp0, abs_of_nonneg hpos]
  exact hlower

/-- There is no global Lipschitz bound for entropy rates in transition distance. -/
theorem conjecture_false :
    ¬ ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ Set.Icc (0 : ℝ) 1, ∀ q ∈ Set.Icc (0 : ℝ) 1,
      |entropyRate (distribution p) (transition p) -
        entropyRate (distribution q) (transition q)| ≤
          C * dist (transition p) (transition q) := by
  rintro ⟨C, hC, hbound⟩
  obtain ⟨p, hp, _, _, hbad⟩ := counterexample C hC
  exact (not_lt_of_ge (hbound p hp 0 ⟨le_rfl, zero_le_one⟩)) hbad

end MarkovEntropy
#print axioms MarkovEntropy.valid_chain
#print axioms MarkovEntropy.entropy_formula
#print axioms MarkovEntropy.transition_distance
#print axioms MarkovEntropy.counterexample
#print axioms MarkovEntropy.conjecture_false
