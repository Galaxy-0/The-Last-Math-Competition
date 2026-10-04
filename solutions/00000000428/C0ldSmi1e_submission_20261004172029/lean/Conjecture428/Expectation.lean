import Conjecture428.Partitions
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-!
# Uniform expectation of the Durfee size

The sample space is the actual finite type `Nat.Partition n`. Its uniform PMF
induces the probability measure used in the Bochner integral below. In
particular, `meanDurfee` is the uniform-partition expectation, and its arithmetic
mean formula is derived from that measure.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Conjecture428

instance partitionMeasurableSpace (n : ℕ) : MeasurableSpace (Nat.Partition n) := ⊤

instance partitionMeasurableSingletonClass (n : ℕ) :
    MeasurableSingletonClass (Nat.Partition n) := ⟨fun _ => trivial⟩

def partitionPMF (n : ℕ) : PMF (Nat.Partition n) :=
  PMF.uniformOfFintype (Nat.Partition n)

def partitionMeasure (n : ℕ) : Measure (Nat.Partition n) :=
  (partitionPMF n).toMeasure

instance partitionMeasure_probability (n : ℕ) : IsProbabilityMeasure (partitionMeasure n) := by
  unfold partitionMeasure
  infer_instance

theorem partitionPMF_apply (n : ℕ) (p : Nat.Partition n) :
    partitionPMF n p = (Fintype.card (Nat.Partition n) : ℝ≥0∞)⁻¹ :=
  PMF.uniformOfFintype_apply p

theorem partitionMeasure_singleton (n : ℕ) (p : Nat.Partition n) :
    partitionMeasure n {p} = (Fintype.card (Nat.Partition n) : ℝ≥0∞)⁻¹ := by
  rw [partitionMeasure, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    partitionPMF_apply]

theorem durfee_measurable (n : ℕ) :
    Measurable (fun p : Nat.Partition n => (durfee p : ℝ)) :=
  measurable_of_finite _

theorem durfee_integrable (n : ℕ) :
    Integrable (fun p : Nat.Partition n => (durfee p : ℝ)) (partitionMeasure n) :=
  Integrable.of_finite

def meanDurfee (n : ℕ) : ℝ :=
  ∫ p : Nat.Partition n, (durfee p : ℝ) ∂partitionMeasure n

/-- The actual integral equals the finite arithmetic mean over all partitions. -/
theorem meanDurfee_eq_average (n : ℕ) :
    meanDurfee n = (∑ p : Nat.Partition n, (durfee p : ℝ)) /
      (Fintype.card (Nat.Partition n) : ℝ) := by
  rw [meanDurfee, partitionMeasure, PMF.integral_eq_sum]
  simp only [partitionPMF_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul]
  rw [← Finset.mul_sum, div_eq_mul_inv, mul_comm]

theorem meanDurfee_nonneg (n : ℕ) : 0 ≤ meanDurfee n :=
  integral_nonneg fun _ => Nat.cast_nonneg _

/-- Averaging preserves the deterministic Durfee-square bound. -/
theorem meanDurfee_le_sqrt (n : ℕ) : meanDurfee n ≤ Real.sqrt (n : ℝ) := by
  calc
    meanDurfee n ≤ ∫ _ : Nat.Partition n, Real.sqrt (n : ℝ) ∂partitionMeasure n :=
      integral_mono (durfee_integrable n) (integrable_const _) fun p => durfee_le_sqrt p
    _ = Real.sqrt (n : ℝ) := by simp

end Conjecture428
