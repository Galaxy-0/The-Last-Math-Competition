import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Data.Complex.FiniteDimensional
import Mathlib.Tactic

noncomputable section
namespace JuliaOrderCounterexample
open Set Metric Filter
open scoped Topology

def f (z : ℂ) : ℂ := Complex.exp (z^5)

theorem entire : Differentiable ℂ f :=
  Complex.differentiable_exp.comp (differentiable_id.pow 5)

-- Actual maximum modulus over the closed disk. For entire functions this
-- agrees with the usual circular maximum; attainment is proved below.
def maximumModulus (g : ℂ → ℂ) (r : ℝ) : ℝ :=
  sSup ((fun z => ‖g z‖) '' {z:ℂ | ‖z‖ ≤ r})

theorem modulus_bound (r : ℝ) (hr : 0 ≤ r) (z : ℂ) (hz : ‖z‖ ≤ r) :
    ‖f z‖ ≤ Real.exp (r^5) := by
  calc
    ‖f z‖ ≤ Real.exp ‖z^5‖ := Complex.norm_exp_le_exp_norm _
    _ = Real.exp (‖z‖^5) := by rw [norm_pow]
    _ ≤ Real.exp (r^5) := Real.exp_le_exp.mpr
      (pow_le_pow_left₀ (norm_nonneg z) hz 5)

theorem real_axis_attains (r : ℝ) : ‖f (r:ℂ)‖ = Real.exp (r^5) := by
  unfold f
  rw [← Complex.ofReal_pow, Complex.norm_exp_ofReal]

theorem maximum_modulus_eq (r : ℝ) (hr : 0 ≤ r) :
    maximumModulus f r = Real.exp (r^5) := by
  have hb : BddAbove ((fun z => ‖f z‖) '' {z:ℂ | ‖z‖ ≤ r}) := by
    refine ⟨Real.exp (r^5), ?_⟩
    rintro y ⟨z,hz,rfl⟩
    exact modulus_bound r hr z hz
  have hn : ((fun z => ‖f z‖) '' {z:ℂ | ‖z‖ ≤ r}).Nonempty :=
    ⟨‖f 0‖, 0, by simpa using hr, rfl⟩
  apply le_antisymm
  · exact csSup_le hn (by rintro y ⟨z,hz,rfl⟩; exact modulus_bound r hr z hz)
  · rw [← real_axis_attains r]
    apply le_csSup hb
    exact ⟨(r:ℂ), by simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr], rfl⟩

def growthRatio (g : ℂ → ℂ) (r : ℝ) : ℝ :=
  Real.log (Real.log (maximumModulus g r)) / Real.log r

def growthOrder (g : ℂ → ℂ) : ℝ := limsup (growthRatio g) atTop

theorem ratio_eq_five (r : ℝ) (hr : 1 < r) : growthRatio f r = 5 := by
  unfold growthRatio
  rw [maximum_modulus_eq r (by linarith), Real.log_exp, Real.log_pow]
  norm_num
  field_simp [ne_of_gt (Real.log_pos hr)]

theorem ratio_limit : Tendsto (growthRatio f) atTop (𝓝 5) := by
  have he : growthRatio f =ᶠ[atTop] (fun _ => (5:ℝ)) := by
    refine eventually_atTop.2 ⟨2, ?_⟩
    intro r hr
    exact ratio_eq_five r (by linarith)
  exact tendsto_const_nhds.congr' he.symm

theorem actual_order : growthOrder f = 5 := ratio_limit.limsup_eq

-- A universal ambient theorem; no substitute definition of a Julia set.
theorem dimension_upper (S : Set ℂ) : dimH S ≤ (2:ENNReal) := by
  calc
    dimH S ≤ dimH (univ:Set ℂ) := dimH_mono (subset_univ _)
    _ = 2 := by rw [Real.dimH_univ_eq_finrank ℂ, Complex.finrank_real_complex]; norm_num

theorem every_planar_set_refutes_bound (S : Set ℂ) :
    ¬ ENNReal.ofReal (growthOrder f / 2) ≤ dimH S := by
  rw [actual_order]
  have hd := dimension_upper S
  intro h
  have he : (2:ENNReal) < ENNReal.ofReal ((5:ℝ)/2) := by norm_num
  exact (not_le_of_gt he) (h.trans hd)

theorem counterexample : Differentiable ℂ f ∧ growthOrder f = 5 ∧
    ∀ S : Set ℂ, ¬ ENNReal.ofReal (growthOrder f / 2) ≤ dimH S :=
  ⟨entire, actual_order, every_planar_set_refutes_bound⟩

end JuliaOrderCounterexample
#print axioms JuliaOrderCounterexample.entire
#print axioms JuliaOrderCounterexample.maximum_modulus_eq
#print axioms JuliaOrderCounterexample.actual_order
#print axioms JuliaOrderCounterexample.dimension_upper
#print axioms JuliaOrderCounterexample.counterexample
