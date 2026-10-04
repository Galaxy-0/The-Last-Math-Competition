import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.NumberTheory.Transcendental.Liouville.LiouvilleNumber
import Mathlib.NumberTheory.Transcendental.Liouville.LiouvilleWith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

noncomputable section
open Filter MeasureTheory
open scoped Topology ENNReal
namespace Counterexample

/-- The classical approximation set at integer parameter w, inside the unit interval.
The approximation error is q^(-(w+1)), with arbitrarily large positive denominators. -/
def jarnikSet (w : ℕ) : Set ℝ :=
  {x | x ∈ Set.Icc 0 1 ∧ Irrational x ∧
    ∀ Q : ℕ, ∃ q : ℕ, Q < q ∧ ∃ p : ℤ,
      0 < |x - (p : ℝ) / q| ∧ |x - (p : ℝ) / q| < 1 / (q : ℝ) ^ (w + 1)}

def L : ℝ := liouvilleNumber 10

theorem L_liouville : Liouville L := liouville_liouvilleNumber (by norm_num)

theorem L_in_unit_interval : L ∈ Set.Icc (0 : ℝ) 1 := by
  have hs := LiouvilleNumber.partialSum_add_remainder (m := (10 : ℝ)) (by norm_num) 1
  have hp := LiouvilleNumber.remainder_pos (m := (10 : ℝ)) (by norm_num) 1
  have hu := LiouvilleNumber.remainder_lt (m := (10 : ℝ)) 1 (by norm_num)
  norm_num [LiouvilleNumber.partialSum, Finset.sum_range_succ] at hs hu
  change 0 ≤ liouvilleNumber 10 ∧ liouvilleNumber 10 ≤ 1
  constructor <;> linarith

theorem L_mem_jarnik (w : ℕ) : L ∈ jarnikSet w := by
  refine ⟨L_in_unit_interval, L_liouville.irrational, ?_⟩
  intro Q
  obtain ⟨q, hq, p, hne, herr⟩ :=
    ((eventually_gt_atTop Q).and_frequently (L_liouville.frequently_exists_num (w + 1))).exists
  exact ⟨q, hq, p, abs_pos.mpr (sub_ne_zero.mpr hne), herr⟩

theorem jarnik_nonempty (w : ℕ) : (jarnikSet w).Nonempty := ⟨L, L_mem_jarnik w⟩

theorem hausdorff_dimension_le_one (w : ℕ) : dimH (jarnikSet w) ≤ 1 := by
  calc dimH (jarnikSet w) ≤ dimH (Set.univ : Set ℝ) := dimH_mono (Set.subset_univ _)
    _ = 1 := Real.dimH_univ

theorem hausdorff_dimension_finite (w : ℕ) : dimH (jarnikSet w) ≠ ∞ :=
  ne_of_lt ((hausdorff_dimension_le_one w).trans_lt ENNReal.one_lt_top)

/-- Finiteness above justifies treating this as the usual real-valued dimension. -/
def dimension (w : ℕ) : ℝ := (dimH (jarnikSet w)).toReal

theorem dimension_bounds (w : ℕ) : 0 ≤ dimension w ∧ dimension w ≤ 1 := by
  refine ⟨ENNReal.toReal_nonneg, ?_⟩
  simpa [dimension] using (ENNReal.toReal_mono (by simp : (1 : ENNReal) ≠ ∞)
    (hausdorff_dimension_le_one w))

theorem dimension_not_claimed : dimension 2 ≠ 2 - ((2 : ℝ) + 1) := by
  have h := (dimension_bounds 2).1
  norm_num
  linarith

theorem counterexample : (jarnikSet 2).Nonempty ∧ dimH (jarnikSet 2) ≠ ∞ ∧
    0 ≤ dimension 2 ∧ dimension 2 ≤ 1 ∧ dimension 2 ≠ 2 - ((2 : ℝ) + 1) :=
  ⟨jarnik_nonempty 2, hausdorff_dimension_finite 2,
    (dimension_bounds 2).1, (dimension_bounds 2).2, dimension_not_claimed⟩

#print axioms L_liouville
#print axioms L_in_unit_interval
#print axioms L_mem_jarnik
#print axioms jarnik_nonempty
#print axioms hausdorff_dimension_finite
#print axioms dimension_bounds
#print axioms dimension_not_claimed
#print axioms counterexample
end Counterexample
