import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

noncomputable section
open Filter
open scoped Topology
namespace Counterexample

abbrev Point := ℤ × ℤ × ℤ

def sphere (m : ℕ) : Set Point :=
  {p | p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 = (m : ℤ)}

def pointHeight (p : Point) : ℝ :=
  max |(p.1 : ℝ)| (max |(p.2.1 : ℝ)| |(p.2.2 : ℝ)|)

def maxHeight (m : ℕ) : ℝ := sSup (pointHeight '' sphere m)

def axis (n : ℕ) : Point := (n, 0, 0)

theorem axis_on_sphere (n : ℕ) : axis n ∈ sphere (n ^ 2) := by
  simp [axis, sphere]

theorem axis_height (n : ℕ) : pointHeight (axis n) = n := by
  simp [pointHeight, axis]

theorem all_heights_le (n : ℕ) {p : Point} (hp : p ∈ sphere (n ^ 2)) :
    pointHeight p ≤ n := by
  have hs : (p.1 : ℝ) ^ 2 + (p.2.1 : ℝ) ^ 2 + (p.2.2 : ℝ) ^ 2 = (n : ℝ) ^ 2 := by
    exact_mod_cast hp
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have ha : |(p.1 : ℝ)| ≤ n := by
    apply abs_le_of_sq_le_sq _ hn
    nlinarith [sq_nonneg (p.2.1 : ℝ), sq_nonneg (p.2.2 : ℝ)]
  have hb : |(p.2.1 : ℝ)| ≤ n := by
    apply abs_le_of_sq_le_sq _ hn
    nlinarith [sq_nonneg (p.1 : ℝ), sq_nonneg (p.2.2 : ℝ)]
  have hc : |(p.2.2 : ℝ)| ≤ n := by
    apply abs_le_of_sq_le_sq _ hn
    nlinarith [sq_nonneg (p.1 : ℝ), sq_nonneg (p.2.1 : ℝ)]
  exact max_le ha (max_le hb hc)

theorem height_set_nonempty (n : ℕ) : (pointHeight '' sphere (n ^ 2)).Nonempty :=
  ⟨pointHeight (axis n), axis n, axis_on_sphere n, rfl⟩

theorem height_set_bounded (n : ℕ) : BddAbove (pointHeight '' sphere (n ^ 2)) := by
  refine ⟨n, ?_⟩
  rintro y ⟨p, hp, rfl⟩
  exact all_heights_le n hp

theorem exact_maximum (n : ℕ) : maxHeight (n ^ 2) = n := by
  apply le_antisymm
  · apply csSup_le (height_set_nonempty n)
    rintro y ⟨p, hp, rfl⟩
    exact all_heights_le n hp
  · have hm : (n : ℝ) ∈ pointHeight '' sphere (n ^ 2) :=
      ⟨axis n, axis_on_sphere n, axis_height n⟩
    exact le_csSup (height_set_bounded n) hm

def predicted (m : ℕ) : ℝ := Real.sqrt ((m : ℝ) / 3)

theorem exact_ratio (n : ℕ) (hn : 0 < n) :
    maxHeight (n ^ 2) / predicted (n ^ 2) = Real.sqrt 3 := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  rw [exact_maximum]
  simp only [predicted, Nat.cast_pow, Real.sqrt_div (sq_nonneg (n : ℝ)),
    Real.sqrt_sq (Nat.cast_nonneg n)]
  field_simp

theorem exact_ratio_third (n : ℕ) (hn : 0 < n) :
    maxHeight (n ^ 2) / (predicted (n ^ 2) / 3) = 3 * Real.sqrt 3 := by
  rw [div_div_eq_mul_div, ← div_mul_eq_mul_div, exact_ratio n hn]
  ring

theorem squares_unbounded : Tendsto (fun n : ℕ => n ^ 2) atTop atTop :=
  tendsto_pow_atTop (by norm_num)

theorem ratio_limit : Tendsto (fun n : ℕ => maxHeight (n ^ 2) / predicted (n ^ 2))
    atTop (𝓝 (Real.sqrt 3)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  exact (exact_ratio n hn).symm

theorem sqrt_three_ne_one : Real.sqrt 3 ≠ 1 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  intro h
  rw [h] at hs
  norm_num at hs

theorem square_ratio_not_one : ¬ Tendsto
    (fun n : ℕ => maxHeight (n ^ 2) / predicted (n ^ 2)) atTop (𝓝 1) := by
  intro h
  exact sqrt_three_ne_one (tendsto_nhds_unique ratio_limit h)

theorem no_claimed_asymptotic : ¬ Tendsto
    (fun m : ℕ => maxHeight m / predicted m) atTop (𝓝 1) := by
  intro h
  exact square_ratio_not_one (h.comp squares_unbounded)

theorem no_third_asymptotic : ¬ Tendsto
    (fun m : ℕ => maxHeight m / (predicted m / 3)) atTop (𝓝 1) := by
  have hlim : Tendsto (fun n : ℕ => maxHeight (n ^ 2) / (predicted (n ^ 2) / 3))
      atTop (𝓝 (3 * Real.sqrt 3)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    exact (exact_ratio_third n hn).symm
  intro h
  have he := tendsto_nhds_unique hlim (h.comp squares_unbounded)
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  nlinarith

#print axioms axis_on_sphere
#print axioms all_heights_le
#print axioms exact_maximum
#print axioms exact_ratio
#print axioms squares_unbounded
#print axioms ratio_limit
#print axioms no_claimed_asymptotic
#print axioms no_third_asymptotic
end Counterexample
