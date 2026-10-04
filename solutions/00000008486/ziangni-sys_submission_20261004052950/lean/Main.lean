import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp

noncomputable section
open MeasureTheory Filter Topology
open scoped NNReal ENNReal BoundedContinuousFunction
namespace FrozenGibbs

abbrev Ω := Fin 2
instance : MeasurableSpace Ω := borel Ω
instance : BorelSpace Ω := ⟨rfl⟩
def T : Ω → Ω := id
def f (x : Ω) : ℝ := x.val
def maximizers : Set Ω := {x | ∀ y, f y ≤ f x}

theorem compact_space : CompactSpace Ω := inferInstance
theorem continuous_T : Continuous T := continuous_id
theorem continuous_f : Continuous f := continuous_of_discreteTopology
theorem maximum_set : maximizers = {1} := by
  ext x
  fin_cases x <;> norm_num [maximizers, f, Fin.forall_fin_two]
theorem maximum_fixed : T 1 = 1 := rfl
theorem maximum_orbit : Set.range (fun n : ℕ => (T^[n]) 1) = maximizers := by
  rw [maximum_set]
  simp [T]

def w (t : ℝ) : ℝ≥0 := ⟨Real.exp (-1 / t), (Real.exp_pos _).le⟩
def p (t : ℝ) : ℝ≥0 := 1 / (1 + w t)
def q (t : ℝ) : ℝ≥0 := w t / (1 + w t)

theorem weights_sum (t : ℝ) : p t + q t = 1 := by
  unfold p q
  rw [← add_div, div_self]
  positivity

def raw (t : ℝ) : Measure Ω := p t • Measure.dirac 0 + q t • Measure.dirac 1

instance raw_probability (t : ℝ) : IsProbabilityMeasure (raw t) where
  measure_univ := by
    simp [raw, ENNReal.smul_def, ← ENNReal.coe_add, weights_sum]

def gibbs (t : ℝ) : ProbabilityMeasure Ω := ⟨raw t, inferInstance⟩
def point (x : Ω) : ProbabilityMeasure Ω := ⟨Measure.dirac x, inferInstance⟩

theorem weights_real (t : ℝ) :
    (p t : ℝ) = 1 / (1 + Real.exp (-1 / t)) ∧
    (q t : ℝ) = Real.exp (-1 / t) / (1 + Real.exp (-1 / t)) := by
  simp [p, q, w]

theorem partition_function (t : ℝ) :
    (∑ x : Ω, Real.exp (-f x / t)) = 1 + Real.exp (-1 / t) := by
  simp [Fin.sum_univ_two, f]

-- Exact point masses relative to counting measure on the two-point space.
theorem gibbs_mass (t : ℝ) (x : Ω) :
    (gibbs t : Measure Ω) {x} =
      ENNReal.ofReal (Real.exp (-f x / t) / ∑ y : Ω, Real.exp (-f y / t)) := by
  rw [partition_function]
  fin_cases x
  · simp only [f, Fin.val_zero, Nat.cast_zero, neg_zero, zero_div, Real.exp_zero]
    rw [← (weights_real t).1]
    simp [gibbs, raw, ENNReal.smul_def]
  · norm_num only [f, Fin.val_one, Nat.cast_one]
    rw [← (weights_real t).2]
    simp [gibbs, raw, ENNReal.smul_def]

theorem integral_gibbs (t : ℝ) (g : Ω →ᵇ ℝ) :
    (∫ x, g x ∂(gibbs t : Measure Ω)) =
      (p t : ℝ) * g 0 + (q t : ℝ) * g 1 := by
  change (∫ x, g x ∂raw t) = _
  rw [raw, integral_add_measure (g.integrable (μ := p t • Measure.dirac 0))
    (g.integrable (μ := q t • Measure.dirac 1)),
    integral_smul_nnreal_measure, integral_smul_nnreal_measure]
  simp [NNReal.smul_def, smul_eq_mul]

theorem weight_limit : Tendsto (fun t : ℝ => Real.exp (-1 / t)) (𝓝[>] 0) (𝓝 0) := by
  have h := Real.tendsto_exp_atBot.comp
    (tendsto_neg_atTop_atBot.comp (tendsto_inv_nhdsGT_zero :
      Tendsto (fun t : ℝ => t⁻¹) (𝓝[>] 0) atTop))
  simpa only [Function.comp_def, neg_div, one_div] using h

theorem p_limit : Tendsto (fun t : ℝ => (p t : ℝ)) (𝓝[>] 0) (𝓝 1) := by
  have hd : Tendsto (fun t : ℝ => 1 + Real.exp (-1 / t)) (𝓝[>] 0) (𝓝 (1 + 0)) :=
    tendsto_const_nhds.add weight_limit
  have hc : Tendsto (fun _ : ℝ => (1 : ℝ)) (𝓝[>] 0) (𝓝 1) := tendsto_const_nhds
  have h : Tendsto (fun t : ℝ => 1 / (1 + Real.exp (-1 / t)))
      (𝓝[>] 0) (𝓝 ((1 : ℝ) / (1 + 0))) :=
    hc.div hd (by norm_num : (1 : ℝ) + 0 ≠ 0)
  simpa [p, w] using h

theorem q_limit : Tendsto (fun t : ℝ => (q t : ℝ)) (𝓝[>] 0) (𝓝 0) := by
  have hd : Tendsto (fun t : ℝ => 1 + Real.exp (-1 / t)) (𝓝[>] 0) (𝓝 (1 + 0)) :=
    tendsto_const_nhds.add weight_limit
  simpa [weights_real] using weight_limit.div hd (by norm_num : (1 : ℝ) + 0 ≠ 0)

theorem weak_limit_minimum : Tendsto gibbs (𝓝[>] 0) (𝓝 (point 0)) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro g
  have h := (p_limit.mul_const (g 0)).add (q_limit.mul_const (g 1))
  simpa only [integral_gibbs, point, ProbabilityMeasure.coe_mk, integral_dirac,
    one_mul, zero_mul, add_zero] using h

theorem point_masses_distinct : point 0 ≠ point 1 := by
  intro h
  have he := congrArg (fun ν : ProbabilityMeasure Ω => (ν : Measure Ω) {0}) h
  norm_num [point] at he

theorem not_weak_limit_maximum : ¬ Tendsto gibbs (𝓝[>] 0) (𝓝 (point 1)) := by
  intro h
  exact point_masses_distinct (tendsto_nhds_unique weak_limit_minimum h)

#print axioms maximum_orbit
#print axioms raw_probability
#print axioms gibbs_mass
#print axioms weak_limit_minimum
#print axioms not_weak_limit_maximum
end FrozenGibbs
