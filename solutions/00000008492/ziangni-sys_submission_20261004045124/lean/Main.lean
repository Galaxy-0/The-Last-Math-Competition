import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

noncomputable section
open MeasureTheory Filter Topology
namespace SubadditiveRate

abbrev Ω := Unit
instance : MeasurableSpace Ω := ⊤
def μ : Measure Ω := Measure.dirac ()
instance : IsProbabilityMeasure μ := by unfold μ; infer_instance
def T : Ω → Ω := id
def X (n : ℕ) (_ : Ω) : ℝ := Real.sqrt n

theorem system_ergodic : Ergodic T μ where
  toMeasurePreserving := MeasurePreserving.id μ
  aeconst_set _ _ _ := Filter.EventuallyConst.of_subsingleton_left

theorem integrable_X (n : ℕ) : Integrable (X n) μ := integrable_const _

theorem expectation_X (n : ℕ) : (∫ ω, X n ω ∂μ) = Real.sqrt n := by
  simp [X]

theorem X_nonneg (n : ℕ) (ω : Ω) : 0 ≤ X n ω := Real.sqrt_nonneg _

theorem X_zero (ω : Ω) : X 0 ω = 0 := by simp [X]

theorem subadditive_process (m n : ℕ) (ω : Ω) :
    X (m + n) ω ≤ X m ω + X n ((T^[m]) ω) := by
  simp only [X, Nat.cast_add]
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · have hm := Real.sq_sqrt (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
    have hn := Real.sq_sqrt (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    have hp : 0 ≤ Real.sqrt m * Real.sqrt n := by positivity
    nlinarith

def mean (n : ℕ) : ℝ := (∫ ω, X n ω ∂μ) / n

theorem mean_eq (n : ℕ) : mean n = Real.sqrt n / n := by
  rw [mean, expectation_X]

theorem mean_tendsto_zero : Tendsto mean atTop (𝓝 0) := by
  have h := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp
    tendsto_natCast_atTop_atTop
  convert h using 1
  funext n
  rw [mean_eq, Real.sqrt_div_self]
  simp only [Function.comp_apply, Real.sqrt_eq_rpow, Real.rpow_neg (Nat.cast_nonneg n)]

theorem pointwise_normalized_limit (ω : Ω) :
    Tendsto (fun n : ℕ => X n ω / n) atTop (𝓝 0) := by
  exact mean_tendsto_zero.congr' (Filter.Eventually.of_forall fun n => mean_eq n)

theorem log_div_sqrt_tendsto_zero :
    Tendsto (fun n : ℕ => Real.log n / Real.sqrt n) atTop (𝓝 0) := by
  have h := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
  simpa only [Real.sqrt_eq_rpow] using h.comp tendsto_natCast_atTop_atTop

theorem no_eventual_rate (C : ℝ) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ 1 ≤ n ∧ C * (Real.log n / n) < mean n := by
  have hlim : Tendsto (fun n : ℕ => C * (Real.log n / Real.sqrt n)) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul log_div_sqrt_tendsto_zero
  have hsmall : ∀ᶠ n : ℕ in atTop, C * (Real.log n / Real.sqrt n) < 1 :=
    hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  obtain ⟨n, hn, hn1, hs⟩ := (eventually_ge_atTop N |>.and
    ((eventually_ge_atTop 1).and hsmall)).exists
  refine ⟨n, hn, hn1, ?_⟩
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn1)
  have hspos : 0 < Real.sqrt n := Real.sqrt_pos.2 hnpos
  have hb : C * Real.log n < Real.sqrt n := by
    rw [← mul_div_assoc, div_lt_one hspos] at hs
    exact hs
  rw [mean_eq, ← mul_div_assoc]
  exact (div_lt_div_iff_of_pos_right hnpos).mpr hb

theorem not_bigO : ¬ Asymptotics.IsBigO atTop mean
    (fun n : ℕ => Real.log n / n) := by
  intro h
  obtain ⟨C, hC⟩ := h.exists_pos
  obtain ⟨N, hN⟩ := eventually_atTop.1 hC.2.bound
  obtain ⟨n, hn, hn1, hlt⟩ := no_eventual_rate C N
  have hp : 0 ≤ Real.log (n : ℝ) / n := by
    apply div_nonneg
    · apply Real.log_nonneg
      exact_mod_cast hn1
    · positivity
  have hm : 0 ≤ mean n := by rw [mean_eq]; positivity
  have hb := hN n hn
  simp only [Real.norm_eq_abs, abs_of_nonneg hp, abs_of_nonneg hm] at hb
  exact (not_lt_of_ge hb) hlt

#print axioms system_ergodic
#print axioms subadditive_process
#print axioms expectation_X
#print axioms mean_tendsto_zero
#print axioms no_eventual_rate
#print axioms not_bigO
end SubadditiveRate
