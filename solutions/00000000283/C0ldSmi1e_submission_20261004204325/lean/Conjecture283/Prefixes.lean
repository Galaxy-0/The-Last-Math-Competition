import Conjecture283.Factors
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Topology.Order.MonotoneConvergence

open scoped BigOperators
open Filter

namespace Conjecture283

/-- The finite «prefix» gains its next actual cosine factor. -/
theorem prefix_succ (n : ℕ) : «prefix» (n + 1) = «prefix» n * factor n := by
  simp only [«prefix», Finset.prod_range_succ]

theorem prefix_pos (n : ℕ) : 0 < «prefix» n := by
  unfold «prefix»
  exact Finset.prod_pos fun k _ => factor_pos k

theorem prefix_antitone : Antitone «prefix» := by
  apply antitone_nat_of_succ_le
  intro n
  rw [prefix_succ]
  exact mul_le_of_le_one_right (le_of_lt (prefix_pos n)) (factor_le_one n)

theorem constant_le_prefix (n : ℕ) : constant ≤ «prefix» n :=
  prefix_antitone.le_of_tendsto tendsto_prefix n

/-- The conjecture's partial product, ending at the polygon size `N`. -/
noncomputable def partialProduct (N : ℕ) : ℝ :=
  ∏ k ∈ Finset.Icc 3 N, Real.cos (Real.pi / (k : ℝ))

/-- A «prefix» with `n` terms has last polygon size `n + 2`. -/
theorem partialProduct_add_two (n : ℕ) : partialProduct (n + 2) = «prefix» n := by
  induction n with
  | zero => simp [partialProduct, «prefix»]
  | succ n ih =>
    rw [show n.succ + 2 = (n + 2) + 1 by omega]
    unfold partialProduct
    rw [Finset.prod_Icc_succ_top (by omega : 3 ≤ n + 2 + 1)]
    change partialProduct (n + 2) * Real.cos (Real.pi / ((n + 2 + 1 : ℕ) : ℝ)) =
      «prefix» (n + 1)
    rw [ih, prefix_succ]
    have hcast : ((n + 2 + 1 : ℕ) : ℝ) = (n : ℝ) + 3 := by
      push_cast
      ring
    rw [hcast]
    rfl

theorem tendsto_partialProduct : Tendsto partialProduct atTop (nhds constant) := by
  apply (tendsto_add_atTop_iff_nat 2).mp
  simpa only [partialProduct_add_two] using tendsto_prefix

/-- The first omitted factor already provides a positive error lower bound. -/
theorem prefix_error_lower (n : ℕ) :
    2 * constant / ((n : ℝ) + 3) ^ 2 ≤ «prefix» n - constant := by
  have hnext := constant_le_prefix (n + 1)
  rw [prefix_succ] at hnext
  have hdeficit : 0 ≤ 1 - factor n := sub_nonneg.mpr (factor_le_one n)
  calc
    2 * constant / ((n : ℝ) + 3) ^ 2 =
        constant * (2 / ((n : ℝ) + 3) ^ 2) := by ring
    _ ≤ constant * (1 - factor n) :=
      mul_le_mul_of_nonneg_left (factor_deficit_lower n) (le_of_lt constant_pos)
    _ ≤ «prefix» n * (1 - factor n) :=
      mul_le_mul_of_nonneg_right (constant_le_prefix n) hdeficit
    _ ≤ «prefix» n - constant := by nlinarith

/-- A lower bound for the error of the actual source partial products. -/
theorem error_lower (N : ℕ) (hN : 3 ≤ N) :
    2 * constant / ((N : ℝ) + 1) ^ 2 ≤ partialProduct N - constant := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le (show 2 ≤ N by omega)
  rw [Nat.add_comm 2 n, partialProduct_add_two]
  have hcast : ((n + 2 : ℕ) : ℝ) + 1 = (n : ℝ) + 3 := by
    push_cast
    ring
  rw [hcast]
  exact prefix_error_lower n

end Conjecture283
