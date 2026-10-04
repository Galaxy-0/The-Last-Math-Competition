import Mathlib.NumberTheory.Transcendental.Liouville.LiouvilleNumber
import Mathlib.NumberTheory.Transcendental.Liouville.LiouvilleWith
import Mathlib.Algebra.Order.Round
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

noncomputable section
open Filter
open scoped Topology
namespace Counterexample

/-- q times the distance from q*x to its nearest integer. -/
def error (x : ℝ) (q : ℕ) : ℝ := (q : ℝ) * |(q : ℝ) * x - round ((q : ℝ) * x)|

/-- The standard reciprocal Lagrange/Hurwitz constant 1/ν(x). -/
def constant (x : ℝ) : ℝ := liminf (error x) atTop

def spectrum : Set ℝ := {c | ∃ x : ℝ, Irrational x ∧ constant x = c}

theorem error_nonneg (x : ℝ) (q : ℕ) : 0 ≤ error x q :=
  mul_nonneg (Nat.cast_nonneg q) (abs_nonneg _)

theorem nearest_integer_minimizes (x : ℝ) (q : ℕ) (p : ℤ) :
    |(q : ℝ) * x - round ((q : ℝ) * x)| ≤ |(q : ℝ) * x - p| :=
  round_le _ _

theorem approximation_bound {x : ℝ} {q : ℕ} (hq : 0 < q) (p : ℤ) :
    error x q ≤ (q : ℝ) ^ 2 * |x - (p : ℝ) / q| := by
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
  have hid : (q : ℝ) * x - p = q * (x - (p : ℝ) / q) := by field_simp; ring
  calc error x q ≤ (q : ℝ) * |(q : ℝ) * x - p| :=
      mul_le_mul_of_nonneg_left (nearest_integer_minimizes x q p) (Nat.cast_nonneg q)
    _ = (q : ℝ) ^ 2 * |x - (p : ℝ) / q| := by
      rw [hid, abs_mul, abs_of_nonneg (Nat.cast_nonneg q)]
      ring

theorem frequently_small {x : ℝ} (hx : Liouville x) {ε : ℝ} (hε : 0 < ε) :
    ∃ᶠ q : ℕ in atTop, error x q ≤ ε := by
  have hinv : Tendsto (fun q : ℕ => 1 / (q : ℝ)) atTop (𝓝 0) := by
    simpa only [one_div] using tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hevent : ∀ᶠ q : ℕ in atTop, 0 < q ∧ 1 / (q : ℝ) < ε :=
    (eventually_gt_atTop 0).and (hinv.eventually (gt_mem_nhds hε))
  apply (hevent.and_frequently (hx.frequently_exists_num 3)).mono
  rintro q ⟨⟨hq, hsmall⟩, p, _, hp⟩
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have he : error x q < 1 / (q : ℝ) := by
    calc error x q ≤ (q : ℝ) ^ 2 * |x - (p : ℝ) / q| := approximation_bound hq p
      _ < (q : ℝ) ^ 2 * (1 / (q : ℝ) ^ 3) := mul_lt_mul_of_pos_left hp (sq_pos_of_pos hqR)
      _ = 1 / (q : ℝ) := by field_simp; ring
  exact (he.trans hsmall).le

theorem liouville_constant_zero {x : ℝ} (hx : Liouville x) : constant x = 0 := by
  have hbounded : atTop.IsBoundedUnder (· ≥ ·) (error x) :=
    isBoundedUnder_of ⟨0, error_nonneg x⟩
  have hcobounded : atTop.IsCoboundedUnder (· ≥ ·) (error x) :=
    IsCoboundedUnder.of_frequently_le (frequently_small hx (by norm_num : (0 : ℝ) < 1))
  apply le_antisymm
  · by_contra h
    have hp : 0 < constant x := lt_of_not_ge h
    have hh : constant x ≤ constant x / 2 :=
      liminf_le_of_frequently_le (frequently_small hx (half_pos hp)) hbounded
    linarith
  · exact le_liminf_of_le hcobounded (Eventually.of_forall (error_nonneg x))

def L : ℝ := liouvilleNumber 10
theorem L_liouville : Liouville L := liouville_liouvilleNumber (by norm_num)
theorem L_irrational : Irrational L := L_liouville.irrational
theorem L_constant_zero : constant L = 0 := liouville_constant_zero L_liouville

theorem zero_mem_spectrum : (0 : ℝ) ∈ spectrum :=
  ⟨L, L_irrational, L_constant_zero⟩

theorem zero_mem_closure : (0 : ℝ) ∈ closure spectrum := subset_closure zero_mem_spectrum

theorem zero_not_claimed_interval : (0 : ℝ) ∉ Set.Icc (1 / Real.sqrt 5) (1 / 2) := by
  have hp : 0 < 1 / Real.sqrt 5 := one_div_pos.mpr (Real.sqrt_pos.mpr (by norm_num))
  intro h
  exact (not_le_of_gt hp) h.1

theorem counterexample : closure spectrum ≠ Set.Icc (1 / Real.sqrt 5) (1 / 2) := by
  intro he
  exact zero_not_claimed_interval (he ▸ zero_mem_closure)

#print axioms nearest_integer_minimizes
#print axioms approximation_bound
#print axioms frequently_small
#print axioms liouville_constant_zero
#print axioms L_irrational
#print axioms L_constant_zero
#print axioms zero_mem_closure
#print axioms counterexample
end Counterexample
