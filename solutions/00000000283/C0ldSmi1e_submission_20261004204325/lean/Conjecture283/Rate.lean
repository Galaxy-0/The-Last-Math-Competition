import Conjecture283.Prefixes
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

open Filter
namespace Conjecture283

/-- A quadratic error lower bound with a positive coefficient precludes a cubic rate. -/
theorem cubic_scaled_unbounded_of_lower
    (e : ℕ → ℝ) (K : ℝ) (hK : 0 < K)
    (hlower : ∀ N : ℕ, 3 ≤ N → 2 * K / ((N : ℝ) + 1)^2 ≤ e N)
    (C : ℝ) (N₀ : ℕ) :
    ∃ N : ℕ, N₀ ≤ N ∧ C < (N : ℝ)^3 * |e N| := by
  obtain ⟨m, hm⟩ := exists_nat_gt (2 * C / K)
  let N := max (max N₀ 3) m
  have hN₀ : N₀ ≤ N := (le_max_left N₀ 3).trans (le_max_left _ m)
  have hN3 : 3 ≤ N := (le_max_right N₀ 3).trans (le_max_left _ m)
  have hmN : m ≤ N := le_max_right _ _
  have hNR : (3 : ℝ) ≤ N := by exact_mod_cast hN3
  have hNpos : (0 : ℝ) < N := by linarith
  have hdpos : 0 < ((N : ℝ) + 1)^2 := sq_pos_of_pos (by linarith)
  have hepos : 0 < e N := lt_of_lt_of_le (div_pos (by positivity) hdpos) (hlower N hN3)
  have hl : 2 * K ≤ e N * ((N : ℝ) + 1)^2 := (div_le_iff₀ hdpos).mp (hlower N hN3)
  have hsq : ((N : ℝ) + 1)^2 ≤ 4 * (N : ℝ)^2 := by nlinarith
  have hu := mul_le_mul_of_nonneg_left hsq (le_of_lt hepos)
  have hb : 2 * K ≤ 4 * e N * (N : ℝ)^2 := by nlinarith
  have hbN := mul_le_mul_of_nonneg_right hb (le_of_lt hNpos)
  have hlarge : 2 * C / K < (N : ℝ) := hm.trans_le (by exact_mod_cast hmN)
  have hCK : 2 * C < (N : ℝ) * K := (div_lt_iff₀ hK).mp hlarge
  refine ⟨N, hN₀, ?_⟩
  rw [abs_of_pos hepos]
  nlinarith

/-- The quantitative obstruction uses the ordinary atTop Big-O definition. -/
theorem not_cubic_bigO_of_lower
    (e : ℕ → ℝ) (K : ℝ) (hK : 0 < K)
    (hlower : ∀ N : ℕ, 3 ≤ N → 2 * K / ((N : ℝ) + 1)^2 ≤ e N) :
    ¬ Asymptotics.IsBigO atTop e (fun N : ℕ => ((N : ℝ)^3)⁻¹) := by
  intro h
  obtain ⟨C, hC⟩ := Asymptotics.isBigO_iff.mp h
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hC
  obtain ⟨N, hN, hbig⟩ := cubic_scaled_unbounded_of_lower e K hK hlower C (max N₀ 3)
  have h3 : 3 ≤ N := (le_max_right N₀ 3).trans hN
  have hpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hbound := hN₀ N ((le_max_left N₀ 3).trans hN)
  simp only [Real.norm_eq_abs, abs_inv, abs_pow, abs_of_nonneg (le_of_lt hpos)] at hbound
  have hb : |e N| * (N : ℝ)^3 ≤ C := by
    have hd : 0 < (N : ℝ)^3 := pow_pos hpos 3
    apply (le_div_iff₀ hd).mp
    simpa only [div_eq_mul_inv] using hbound
  nlinarith

/-- The error after scaling by the asserted cubic rate is unbounded on every tail. -/
theorem cubic_scaled_error_unbounded (C : ℝ) (N₀ : ℕ) :
    ∃ N : ℕ, N₀ ≤ N ∧ C < (N : ℝ)^3 * |partialProduct N - constant| :=
  cubic_scaled_unbounded_of_lower (fun N => partialProduct N - constant)
    constant constant_pos error_lower C N₀

/-- An explicit violation of every proposed cubic bound beyond every cutoff. -/
theorem cubic_bound_counterexample (C : ℝ) (N₀ : ℕ) :
    ∃ N : ℕ, max N₀ 3 ≤ N ∧ C / (N : ℝ)^3 < |partialProduct N - constant| := by
  obtain ⟨N, hN, hbig⟩ := cubic_scaled_error_unbounded C (max N₀ 3)
  have h3 : 3 ≤ N := (le_max_right N₀ 3).trans hN
  have hpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  refine ⟨N, hN, (div_lt_iff₀ (pow_pos hpos 3)).mpr ?_⟩
  simpa only [mul_comm] using hbig

/-- The standard cubic upper-bound interpretation of the source's rate clause. -/
def CubicConvergence : Prop :=
  Asymptotics.IsBigO atTop (fun N : ℕ => partialProduct N - constant)
    (fun N : ℕ => ((N : ℝ)^3)⁻¹)

theorem not_cubic_convergence : ¬ CubicConvergence :=
  not_cubic_bigO_of_lower (fun N => partialProduct N - constant)
    constant constant_pos error_lower

end Conjecture283
