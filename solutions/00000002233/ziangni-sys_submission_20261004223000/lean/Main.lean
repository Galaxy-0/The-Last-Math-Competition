import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

noncomputable section
namespace ShiftDifferenceCounterexample
open Set Metric Filter MeasureTheory
open scoped Topology BigOperators

def f (z : ℂ) : ℂ := Complex.exp z
def difference (z : ℂ) : ℂ := f (z+1)-f z

theorem entire : Differentiable ℂ f := Complex.differentiable_exp

theorem difference_formula (z : ℂ) : difference z = (Complex.exp 1-1)*f z := by
  simp only [difference, f, Complex.exp_add]
  ring

theorem coefficient_nonzero : Complex.exp 1-1 ≠ 0 := by
  have he : Real.exp 1 ≠ 1 := by
    intro h
    have hh := Real.exp_lt_exp.mpr (show (0:ℝ)<1 by norm_num)
    simp [h] at hh
  change Complex.exp ((1:ℝ):ℂ)-1 ≠ 0
  rw [← Complex.ofReal_exp]
  apply sub_ne_zero.mpr
  exact_mod_cast he

theorem zero_free (z : ℂ) : difference z ≠ 0 := by
  rw [difference_formula]
  exact mul_ne_zero coefficient_nonzero (Complex.exp_ne_zero z)

def diskZeros (r : ℝ) : Set ℂ := {z | ‖z‖ ≤ r ∧ difference z = 0}

theorem disk_zeros_empty (r : ℝ) : diskZeros r = ∅ := by
  ext z
  simp only [diskZeros, mem_setOf_eq, mem_empty_iff_false, iff_false]
  exact fun hz => zero_free z hz.2

def zeroPoints (r : ℝ) : Finset ℂ :=
  (show (diskZeros r).Finite from by rw [disk_zeros_empty]; exact finite_empty).toFinset

theorem zero_points_empty (r : ℝ) : zeroPoints r = ∅ := by
  ext z
  simp [zeroPoints,disk_zeros_empty]

-- Quantification over every weight covers actual zero multiplicities.
def weightedCount (w : ℂ → ℝ) (r : ℝ) : ℝ := ∑ z ∈ zeroPoints r, w z

theorem weighted_count_zero (w : ℂ → ℝ) (r : ℝ) : weightedCount w r = 0 := by
  simp [weightedCount,zero_points_empty]

def integratedCount (w : ℂ → ℝ) (r : ℝ) : ℝ :=
  ∫ t in (0:ℝ)..r, weightedCount w t / t

theorem integrated_count_zero (w : ℂ → ℝ) (r : ℝ) : integratedCount w r = 0 := by
  simp [integratedCount,weighted_count_zero]

def maximumModulus (r : ℝ) : ℝ := sSup ((fun z:ℂ => ‖f z‖) '' {z | ‖z‖ ≤ r})

theorem modulus_bound (r : ℝ) (z : ℂ) (hz : ‖z‖ ≤ r) : ‖f z‖ ≤ Real.exp r :=
  (Complex.norm_exp_le_exp_norm z).trans (Real.exp_le_exp.mpr hz)

theorem maximum_eq (r : ℝ) (hr : 0 ≤ r) : maximumModulus r = Real.exp r := by
  have hb : BddAbove ((fun z:ℂ => ‖f z‖) '' {z | ‖z‖ ≤ r}) := by
    refine ⟨Real.exp r, ?_⟩
    rintro y ⟨z,hz,rfl⟩
    exact modulus_bound r z hz
  have hn : ((fun z:ℂ => ‖f z‖) '' {z | ‖z‖ ≤ r}).Nonempty :=
    ⟨‖f 0‖,0,by simpa using hr,rfl⟩
  apply le_antisymm
  · exact csSup_le hn (by rintro y ⟨z,hz,rfl⟩; exact modulus_bound r z hz)
  · change Real.exp r ≤ sSup _
    rw [← Complex.norm_exp_ofReal r]
    exact le_csSup hb ⟨(r:ℂ),by simpa [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hr],rfl⟩

def growthRatio (r : ℝ) : ℝ := Real.log (Real.log (maximumModulus r)) / Real.log r
def growthOrder : ℝ := limsup growthRatio atTop

theorem ratio_eq (r : ℝ) (hr : 1 < r) : growthRatio r = 1 := by
  unfold growthRatio
  rw [maximum_eq r (by linarith),Real.log_exp]
  exact div_self (ne_of_gt (Real.log_pos hr))

theorem integer_order : growthOrder = 1 := by
  have he : growthRatio =ᶠ[atTop] (fun _ => (1:ℝ)) := by
    refine eventually_atTop.2 ⟨2, ?_⟩
    intro r hr
    exact ratio_eq r (by linarith)
  exact (tendsto_const_nhds.congr' he.symm).limsup_eq

-- Actual circle parameter and Nevanlinna proximity integral; f has no poles.
def circlePoint (r theta : ℝ) : ℂ := (r:ℂ)*Complex.exp ((theta:ℂ)*Complex.I)
def kernel (r theta : ℝ) : ℝ := max 0 (Real.log ‖f (circlePoint r theta)‖)
def characteristic (r : ℝ) : ℝ :=
  (1/(2*Real.pi)) * ∫ theta in (-Real.pi)..Real.pi, kernel r theta

theorem kernel_eq (r theta : ℝ) : kernel r theta = max 0 (r*Real.cos theta) := by
  simp [kernel,f,Complex.norm_exp,Real.log_exp,circlePoint,Complex.mul_re,
    Complex.exp_ofReal_mul_I_re]

theorem characteristic_positive (r : ℝ) (hr : 0 < r) : 0 < characteristic r := by
  unfold characteristic
  apply mul_pos
  · exact one_div_pos.mpr (mul_pos (by norm_num) Real.pi_pos)
  · simp_rw [kernel_eq]
    apply intervalIntegral.integral_pos (by linarith [Real.pi_pos])
    · exact (continuous_const.max (continuous_const.mul Real.continuous_cos)).continuousOn
    · intro theta htheta; exact le_max_left _ _
    · refine ⟨0, ?_, ?_⟩
      · constructor <;> linarith [Real.pi_pos]
      · simpa [max_eq_right hr.le] using hr

theorem lower_bound_fails (w : ℂ → ℝ) (r : ℝ) (hr : 0 < r) :
    ¬ characteristic r * (1-(1/2:ℝ)) ≤ integratedCount w r := by
  rw [integrated_count_zero]
  have h := characteristic_positive r hr
  norm_num
  linarith

theorem arbitrarily_large_failure (w : ℂ → ℝ) (R : ℝ) :
    ∃ r > R, 0 < r ∧ ¬ characteristic r * (1-(1/2:ℝ)) ≤ integratedCount w r := by
  refine ⟨max R 1+1, ?_, ?_, ?_⟩
  · linarith [le_max_left R 1]
  · linarith [le_max_right R 1]
  · exact lower_bound_fails w _ (by linarith [le_max_right R 1])

end ShiftDifferenceCounterexample
#print axioms ShiftDifferenceCounterexample.entire
#print axioms ShiftDifferenceCounterexample.zero_free
#print axioms ShiftDifferenceCounterexample.integer_order
#print axioms ShiftDifferenceCounterexample.weighted_count_zero
#print axioms ShiftDifferenceCounterexample.characteristic_positive
#print axioms ShiftDifferenceCounterexample.arbitrarily_large_failure
