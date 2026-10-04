import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

open Filter MeasureTheory
open scoped Topology
noncomputable section
namespace AnalyticBasin

def objective (x : ℝ) : ℝ := x^3
theorem analytic (x : ℝ) : AnalyticAt ℝ objective x :=
  analyticAt_id.pow 3

theorem objective_derivative (x : ℝ) :
    HasDerivAt objective (3*x^2) x := by
  simpa [objective] using (hasDerivAt_id x).pow 3
theorem actual_gradient (x : ℝ) : gradient objective x = 3*x^2 := by
  rw [gradient_eq_deriv', (objective_derivative x).deriv]
theorem stationary : gradient objective 0 = 0 := by rw [actual_gradient]; norm_num

theorem not_local_min : ¬ IsLocalMin objective 0 := by
  intro h
  have hn : {q : ℝ | objective 0 ≤ objective q} ∈ nhds (0 : ℝ) := h
  rcases Metric.mem_nhds_iff.mp hn with ⟨ε,hε,hball⟩
  have hb : -ε/2 ∈ Metric.ball (0 : ℝ) ε := by
    simp only [Metric.mem_ball, Real.dist_eq, sub_zero]
    rw [abs_of_neg (by linarith : -ε/2 < 0)]
    linarith
  have hh := hball hb
  have hneg : (-ε/2)^3 < (0 : ℝ) := by
    have ht : -ε/2 < 0 := by linarith
    have hs : 0 < (-ε/2)^2 := sq_pos_of_ne_zero (ne_of_lt ht)
    nlinarith
  exact (not_le_of_gt hneg) (by simpa [objective] using hh)

def flow (s t : ℝ) : ℝ := s/(1+3*s*t)
theorem denominator_positive {s t : ℝ} (hs : 0 < s) (ht : 0 ≤ t) :
    0 < 1+3*s*t := by positivity

theorem flow_initial (s : ℝ) : flow s 0 = s := by simp [flow]
theorem flow_derivative {s t : ℝ} (hs : 0 < s) (ht : 0 ≤ t) :
    HasDerivAt (flow s) (-gradient objective (flow s t)) t := by
  have hn : 1+3*s*t ≠ 0 := ne_of_gt (denominator_positive hs ht)
  have hd := (hasDerivAt_const t s).div
    (((hasDerivAt_id t).const_mul (3*s)).const_add 1) hn
  convert hd using 1
  rw [actual_gradient]
  dsimp [flow]
  field_simp
  ring

theorem flow_limit {s : ℝ} (hs : 0 < s) :
    Tendsto (flow s) atTop (𝓝 0) := by
  have ha : Tendsto (fun t : ℝ => 1+3*s*t) atTop atTop := by
    have hmul := tendsto_id.const_mul_atTop (by positivity : 0 < 3*s)
    simpa only [add_comm] using tendsto_atTop_add_const_left atTop 1 hmul
  have hi := tendsto_inv_atTop_zero.comp ha
  simpa [flow, div_eq_mul_inv] using hi.const_mul s

-- Full forward gradient-flow definition, quantified over all nonnegative real times.
def Basin : Set ℝ := {s | ∃ u : ℝ → ℝ, u 0 = s ∧
    (∀ t, 0 ≤ t → HasDerivAt u (-gradient objective (u t)) t) ∧
    Tendsto u atTop (𝓝 0)}

theorem positive_starts_in_basin {s : ℝ} (hs : 0 < s) : s ∈ Basin :=
  ⟨flow s, flow_initial s, fun _ ht => flow_derivative hs ht, flow_limit hs⟩

theorem interval_in_basin : Set.Ioo (0 : ℝ) 1 ⊆ Basin := by
  intro s hs
  exact positive_starts_in_basin hs.1

theorem basin_positive_measure : (1 : ENNReal) ≤ volume Basin := by
  have hm : volume (Set.Ioo (0 : ℝ) 1) ≤ volume Basin :=
    measure_mono interval_in_basin
  simpa [Real.volume_Ioo] using hm

theorem basin_not_null : volume Basin ≠ 0 := by
  intro h
  have hh := basin_positive_measure
  rw [h] at hh
  exact (by norm_num : ¬ (1 : ENNReal) ≤ 0) hh

theorem counterexample :
    (∀ x, AnalyticAt ℝ objective x) ∧
    gradient objective 0 = 0 ∧ ¬ IsLocalMin objective 0 ∧
    (∀ s, 0 < s → s ∈ Basin) ∧
    Set.Ioo (0 : ℝ) 1 ⊆ Basin ∧
    (1 : ENNReal) ≤ volume Basin ∧ volume Basin ≠ 0 :=
  ⟨analytic, stationary, not_local_min, fun _ hs => positive_starts_in_basin hs,
    interval_in_basin, basin_positive_measure, basin_not_null⟩

#print axioms analytic
#print axioms actual_gradient
#print axioms stationary
#print axioms not_local_min
#print axioms flow_initial
#print axioms flow_derivative
#print axioms flow_limit
#print axioms interval_in_basin
#print axioms basin_positive_measure
#print axioms counterexample
end AnalyticBasin
