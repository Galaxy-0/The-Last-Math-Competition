import Mathlib.Data.Nat.PrimeFin
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

namespace Conjecture464

open Filter

/-- Number of vertices in our power-of-two cycle family. -/
def vertexCount (k : ℕ) : ℕ := 2 ^ (k + 2)

/-- Maximum of the finite set of prime divisors (zero for an empty set). -/
def largestPrimeFactor (n : ℕ) : ℕ := n.primeFactors.sup id

lemma vertexCount_ge_four (k : ℕ) : 4 ≤ vertexCount k := by
  unfold vertexCount
  calc
    4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ (k + 2) := Nat.pow_le_pow_right (by omega) (by omega)

lemma largestPrimeFactor_vertexCount (k : ℕ) :
    largestPrimeFactor (vertexCount k) = 2 := by
  unfold largestPrimeFactor vertexCount
  rw [Nat.primeFactors_prime_pow (by omega) Nat.prime_two]
  simp

lemma vertexCount_tendsto : Tendsto vertexCount atTop atTop := by
  exact (Nat.tendsto_pow_atTop_atTop_of_one_lt (by norm_num : 1 < (2 : ℕ))).comp
    (tendsto_add_atTop_nat 2)

lemma log_vertexCount_tendsto :
    Tendsto (fun k ↦ Real.log (vertexCount k : ℝ)) atTop atTop := by
  exact Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp vertexCount_tendsto)

lemma eventually_bound_exceeds_two (c : ℝ) (hc : 0 < c) :
    ∀ᶠ k in atTop, (2 : ℝ) < c * Real.log (vertexCount k : ℝ) := by
  exact (log_vertexCount_tendsto.const_mul_atTop hc).eventually (eventually_gt_atTop 2)

/-- Every positive logarithmic lower bound fails eventually, not just at a few small sizes. -/
lemma eventually_primeFactor_lt_bound (c : ℝ) (hc : 0 < c) :
    ∀ᶠ k in atTop,
      (largestPrimeFactor (vertexCount k) : ℝ) < c * Real.log (vertexCount k : ℝ) := by
  simpa only [largestPrimeFactor_vertexCount, Nat.cast_ofNat] using
    eventually_bound_exceeds_two c hc

end Conjecture464
