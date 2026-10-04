import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Tactic.NormNum

/-! An explicit counterexample to the smallest-hit clause of TLMC 00000008178.
The radical is computed from the actual set of prime divisors, not supplied data.
-/

namespace ABC8178

def radical (n : ℕ) : ℕ := n.primeFactors.prod id

def ABCTriple (a b c : ℕ) : Prop :=
  0 < a ∧ a < b ∧ a + b = c ∧
    Nat.Coprime a b ∧ Nat.Coprime a c ∧ Nat.Coprime b c

def ABCHit (a b c : ℕ) : Prop :=
  ABCTriple a b c ∧ radical (a * b * c) < c

def CutoffHit (ε : ℝ) (a b c : ℕ) : Prop :=
  ABCHit a b c ∧ (radical (a * b * c) : ℝ) ≤ (c : ℝ) ^ (1 - ε)

theorem witness_primeFactors : (3 * 125 * 128 : ℕ).primeFactors = {2, 3, 5} := by
  have h125 : (125 : ℕ) = 5 ^ 3 := by norm_num
  have h128 : (128 : ℕ) = 2 ^ 7 := by norm_num
  rw [Nat.primeFactors_mul (by decide) (by decide),
    Nat.primeFactors_mul (by decide) (by decide), h125, h128]
  rw [Nat.primeFactors_prime_pow (p := 5) (by decide) (by decide),
    Nat.primeFactors_prime_pow (p := 2) (by decide) (by decide),
    Nat.Prime.primeFactors (by decide : Nat.Prime 3)]
  decide

theorem witness_radical : radical (3 * 125 * 128) = 30 := by
  unfold radical
  rw [witness_primeFactors]
  decide

theorem witness_triple : ABCTriple 3 125 128 := by
  unfold ABCTriple
  decide

theorem witness_hit : ABCHit 3 125 128 := by
  exact ⟨witness_triple, by rw [witness_radical]; decide⟩

theorem witness_cutoff_bound : (30 : ℝ) ≤ (128 : ℝ) ^ (1 - (1 / 4 : ℝ)) := by
  apply (Real.rpow_le_rpow_iff (by norm_num) (Real.rpow_nonneg (by norm_num) _) (by norm_num : (0 : ℝ) < 4)).mp
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 128)]
  norm_num

theorem witness_cutoff : CutoffHit (1 / 4) 3 125 128 := by
  refine ⟨witness_hit, ?_⟩
  rw [witness_radical]
  exact witness_cutoff_bound

/-- The usual minimum ordering is by c = a + b. -/
def IsSmallestHit (c₀ : ℕ) : Prop :=
  ∀ a b c : ℕ, ABCHit a b c → c₀ ≤ c

/-- Also test minimality in the explicitly stated fixed-epsilon cutoff class. -/
def IsSmallestCutoffHit (ε : ℝ) (c₀ : ℕ) : Prop :=
  ∀ a b c : ℕ, CutoffHit ε a b c → c₀ ≤ c

theorem claimed_sum : 2 + 3 ^ 10 * 109 = (23 ^ 5 : ℕ) := by decide

theorem smaller : 128 < (23 ^ 5 : ℕ) := by decide

theorem not_smallest_hit : ¬ IsSmallestHit (23 ^ 5) := by
  intro h
  exact (Nat.not_le_of_lt smaller) (h 3 125 128 witness_hit)

theorem not_smallest_cutoff_hit : ¬ IsSmallestCutoffHit (1 / 4) (23 ^ 5) := by
  intro h
  exact (Nat.not_le_of_lt smaller) (h 3 125 128 witness_cutoff)

/-- A positive admissible epsilon and a concrete smaller hit refute minimality. -/
theorem counterexample :
    0 < (1 / 4 : ℝ) ∧ (1 / 4 : ℝ) < 1 ∧
    CutoffHit (1 / 4) 3 125 128 ∧ 128 < (23 ^ 5 : ℕ) ∧
    ¬ IsSmallestHit (23 ^ 5) ∧ ¬ IsSmallestCutoffHit (1 / 4) (23 ^ 5) := by
  exact ⟨by norm_num, by norm_num, witness_cutoff, smaller,
    not_smallest_hit, not_smallest_cutoff_hit⟩

end ABC8178

#print axioms ABC8178.counterexample
