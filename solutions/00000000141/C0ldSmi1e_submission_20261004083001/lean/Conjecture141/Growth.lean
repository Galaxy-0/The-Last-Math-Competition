import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-! The conjectured expression grows more slowly than the factorial family. -/
noncomputable section
open Filter
open scoped Topology

namespace Conjecture141

/-- The exact proposed asymptotic expression, with its leading constant left arbitrary. -/
def proposedCount (c : ℝ) (n : ℕ) : ℝ :=
  c * (n : ℝ) ^ (-(1 : ℝ) / 2) *
    Real.exp (2 * Real.sqrt ((n : ℝ) / Real.log (n : ℝ)))

/-- The explicit constant printed in the conjecture. -/
def sourceConstant : ℝ :=
  (4 * Real.pi) ^ (-(1 : ℝ) / 2) * Real.exp (-(1 : ℝ) / 2)

theorem sourceConstant_pos : 0 < sourceConstant := by
  unfold sourceConstant
  positivity

theorem proposedCount_pos (c : ℝ) (hc : 0 < c) (n : ℕ) (hn : 0 < n) :
    0 < proposedCount c n := by
  unfold proposedCount
  positivity

/-- A coarse exponential bound suffices; no asymptotic expansion is assumed. -/
theorem proposedCount_le_exp (c : ℝ) (hc : 0 ≤ c) (n : ℕ)
    (hn : 4 ≤ (n : ℝ)) (hlog : 1 ≤ Real.log (n : ℝ)) :
    proposedCount c n ≤ c * Real.exp (n : ℝ) := by
  have hn0 : 0 ≤ (n : ℝ) := by positivity
  have hsqrt : 2 * Real.sqrt ((n : ℝ) / Real.log (n : ℝ)) ≤ (n : ℝ) := by
    have hmono := Real.sqrt_le_sqrt (div_le_self hn0 hlog)
    have hsquare := Real.sq_sqrt hn0
    have hsnonneg := Real.sqrt_nonneg (n : ℝ)
    have hlarge : 2 ≤ Real.sqrt (n : ℝ) := by nlinarith
    nlinarith [sq_nonneg (Real.sqrt (n : ℝ) - 2)]
  have hpow : (n : ℝ) ^ (-(1 : ℝ) / 2) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
  unfold proposedCount
  calc
    c * (n : ℝ) ^ (-(1 : ℝ) / 2) *
        Real.exp (2 * Real.sqrt ((n : ℝ) / Real.log (n : ℝ)))
        ≤ c * 1 * Real.exp (2 * Real.sqrt ((n : ℝ) / Real.log (n : ℝ))) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hc) (Real.exp_pos _).le
    _ ≤ c * Real.exp (n : ℝ) := by
      simpa using mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hsqrt) hc

/-- Factorials eventually exceed every fixed multiple of a geometric sequence. -/
theorem factorial_eventually_gt_geometric (a c : ℝ) :
    ∀ᶠ n : ℕ in atTop, c * a ^ n < (n.factorial : ℝ) := by
  have hlim := (Real.summable_pow_div_factorial a).tendsto_atTop_zero.const_mul c
  have hsmall : ∀ᶠ n : ℕ in atTop, c * (a ^ n / (n.factorial : ℝ)) < 1 :=
    (by simpa using hlim : Tendsto _ atTop (𝓝 (0 : ℝ))).eventually_lt_const (by norm_num)
  filter_upwards [hsmall] with n hn
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
  exact (div_lt_one hf).mp (by simpa [mul_div_assoc] using hn)

/-- Any actual counting function with the factorial lower bound on even indices
cannot have the proposed asymptotic, for any positive leading constant. -/
theorem no_proposed_asymptotic_of_factorial_lower
    (count : ℕ → ℕ) (hlower : ∀ n, n.factorial ≤ count (2 * n))
    (c : ℝ) (hc : 0 < c) :
    ¬ Tendsto (fun n : ℕ => (count n : ℝ) / proposedCount c n) atTop (𝓝 1) := by
  intro hlim
  have heven : Tendsto (fun n : ℕ => 2 * n) atTop atTop := by
    apply tendsto_atTop_atTop.mpr
    intro b
    exact ⟨b, fun a ha => by omega⟩
  have hx : Tendsto (fun n : ℕ => ((2 * n : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp heven
  have hfour := hx.eventually_ge_atTop 4
  have hlog := (Real.tendsto_log_atTop.comp hx).eventually_ge_atTop 1
  have hratio := (hlim.comp heven).eventually_lt_const (by norm_num : (1 : ℝ) < 2)
  have hfact := factorial_eventually_gt_geometric (Real.exp 2) (2 * c)
  obtain ⟨n, hn4, hnlog, hnratio, hnfac⟩ := (hfour.and (hlog.and (hratio.and hfact))).exists
  have hnpos : 0 < 2 * n := by exact_mod_cast (show (0 : ℝ) < (2 * n : ℕ) by linarith)
  have hgpos := proposedCount_pos c hc (2 * n) hnpos
  have hnum : (count (2 * n) : ℝ) < 2 * proposedCount c (2 * n) :=
    (div_lt_iff₀ hgpos).mp hnratio
  have hbound : proposedCount c (2 * n) ≤ c * (Real.exp 2) ^ n := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat, mul_comm (2 : ℝ) (n : ℝ),
      Real.exp_nat_mul] using proposedCount_le_exp c hc.le (2 * n) hn4 hnlog
  have hcount : (n.factorial : ℝ) ≤ count (2 * n) := by exact_mod_cast hlower n
  nlinarith

end Conjecture141
