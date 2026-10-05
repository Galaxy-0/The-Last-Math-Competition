import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic

noncomputable section
open Filter
open scoped BigOperators Topology

namespace Conjecture283

/-- The cosine factors, starting with the inscribed triangle. -/
def factor (n : ℕ) : ℝ := Real.cos (Real.pi / ((n : ℝ) + 3))

/-- The product of the first `n` factors. -/
def «prefix» (n : ℕ) : ℝ := ∏ k ∈ Finset.range n, factor k

/-- The actual infinite product defining the Kepler–Bouwkamp constant. -/
def constant : ℝ := ∏' n, factor n

theorem factor_pos (n : ℕ) : 0 < factor n := by
  apply Real.cos_pos_of_mem_Ioo
  have hd : 0 < (n : ℝ) + 3 := by positivity
  have ha : 0 < Real.pi / ((n : ℝ) + 3) := div_pos Real.pi_pos hd
  constructor
  · linarith [Real.pi_pos]
  · apply (div_lt_div_iff₀ hd (by norm_num : (0 : ℝ) < 2)).mpr
    nlinarith [Real.pi_pos, mul_nonneg Real.pi_pos.le (Nat.cast_nonneg (α := ℝ) n)]

theorem factor_le_one (n : ℕ) : factor n ≤ 1 := Real.cos_le_one _

theorem factor_deficit_nonneg (n : ℕ) : 0 ≤ 1 - factor n :=
  sub_nonneg.mpr (factor_le_one n)

/-- An explicit lower bound for each cosine deficit. -/
theorem factor_deficit_lower (n : ℕ) :
    2 / ((n : ℝ) + 3) ^ 2 ≤ 1 - factor n := by
  have hd : 0 < (n : ℝ) + 3 := by positivity
  have ha : |Real.pi / ((n : ℝ) + 3)| ≤ Real.pi := by
    rw [abs_of_pos (div_pos Real.pi_pos hd)]
    apply (div_le_iff₀ hd).mpr
    nlinarith [Real.pi_pos, mul_nonneg Real.pi_pos.le (Nat.cast_nonneg (α := ℝ) n)]
  have hb := Real.cos_le_one_sub_mul_cos_sq ha
  have he : 2 / Real.pi ^ 2 * (Real.pi / ((n : ℝ) + 3)) ^ 2 =
      2 / ((n : ℝ) + 3) ^ 2 := by
    field_simp
  rw [he] at hb
  exact (le_sub_comm).mp hb

/-- The matching summable upper bound, obtained from the quadratic cosine estimate. -/
theorem factor_deficit_upper (n : ℕ) :
    1 - factor n ≤ (Real.pi ^ 2 / 2) / ((n : ℝ) + 3) ^ 2 := by
  have h := Real.one_sub_sq_div_two_le_cos (x := Real.pi / ((n : ℝ) + 3))
  have he : (Real.pi / ((n : ℝ) + 3)) ^ 2 / 2 =
      (Real.pi ^ 2 / 2) / ((n : ℝ) + 3) ^ 2 := by
    rw [div_pow]
    ring
  rw [he] at h
  exact (sub_le_comm).mp h

theorem summable_factor_sub_one : Summable (fun n => factor n - 1) := by
  have hp : Summable (fun n : ℕ => 1 / ((n : ℝ) + 3) ^ 2) := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using
      (summable_nat_add_iff 3).mpr
        (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ)))
  have hmajor : Summable (fun n : ℕ => (Real.pi ^ 2 / 2) / ((n : ℝ) + 3) ^ 2) := by
    simpa only [mul_one_div] using hp.mul_left (Real.pi ^ 2 / 2)
  apply hmajor.of_norm_bounded
  intro n
  rw [Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr (factor_le_one n))]
  simpa only [neg_sub] using factor_deficit_upper n

theorem summable_log_factor : Summable (fun n => Real.log (factor n)) := by
  simpa only [add_sub_cancel] using
    Real.summable_log_one_add_of_summable summable_factor_sub_one

/-- The infinite product is an exponential of a convergent real logarithm series. -/
theorem constant_eq_exp_logSum : constant = Real.exp (∑' n, Real.log (factor n)) :=
  (Real.rexp_tsum_eq_tprod factor_pos summable_log_factor).symm

theorem constant_pos : 0 < constant := by
  rw [constant_eq_exp_logSum]
  exact Real.exp_pos _

theorem hasProd_factor : HasProd factor constant := by
  rw [constant_eq_exp_logSum]
  exact Real.hasProd_of_hasSum_log factor_pos summable_log_factor.hasSum

/-- The genuine finite prefixes converge to the genuine infinite product. -/
theorem tendsto_prefix : Tendsto «prefix» atTop (𝓝 constant) :=
  hasProd_factor.tendsto_prod_nat

end Conjecture283
