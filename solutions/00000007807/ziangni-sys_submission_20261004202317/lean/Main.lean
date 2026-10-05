import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.Tactic

noncomputable section
namespace BoundaryLSICounterexample
open Set MeasureTheory Metric

def K : Set ℝ := Icc (-1) 1

theorem body : IsCompact K ∧ Convex ℝ K ∧ (interior K).Nonempty := by
  exact ⟨isCompact_Icc,convex_Icc _ _,⟨0,by norm_num [K,interior_Icc]⟩⟩

theorem boundary : frontier K = ({-1,1}:Set ℝ) := by
  exact frontier_Icc (by norm_num)

def surface : Measure ℝ := (Measure.hausdorffMeasure (0:ℝ)).restrict (frontier K)

theorem surface_eq : surface = Measure.dirac (-1) + Measure.dirac (1:ℝ) := by
  unfold surface
  rw [boundary]
  have hp : ({-1,1}:Set ℝ) = {-1} ∪ {1} := by ext x; simp [or_comm]
  rw [hp,Measure.restrict_union (by norm_num : Disjoint ({-1}:Set ℝ) {1})
    (measurableSet_singleton 1)]
  simp [Measure.hausdorffMeasure_zero_singleton]

theorem surface_mass : surface univ = 2 := by
  rw [surface_eq]
  norm_num

def sigma : Measure ℝ := (2:ENNReal)⁻¹ • surface

theorem sigma_mass : sigma univ = 1 := by
  rw [sigma,Measure.smul_apply,surface_mass]
  exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)

instance : IsProbabilityMeasure sigma := ⟨sigma_mass⟩

def surfaceVolumeRatio : ℝ := (surface univ).toReal / (volume K).toReal

theorem ratio_one : surfaceVolumeRatio = 1 := by
  norm_num [surfaceVolumeRatio,surface_mass,K,Real.volume_Icc]

theorem integral_sigma (q : ℝ → ℝ) : (∫ x, q x ∂sigma) = (q (-1)+q 1)/2 := by
  rw [sigma,surface_eq,integral_smul_measure,
    integral_add_measure integrable_dirac integrable_dirac]
  simp only [integral_dirac]
  norm_num
  ring

def P (x : ℝ) : ℝ := (2+3*x-x^3)/4

theorem smooth : ContDiff ℝ ⊤ P := by unfold P; simp only [div_eq_mul_inv]; fun_prop

theorem derivative (x : ℝ) : HasDerivAt P ((3-3*x^2)/4) x := by
  unfold P
  convert (((hasDerivAt_const x (2:ℝ)).add
    ((hasDerivAt_id x).const_mul 3)).sub ((hasDerivAt_id x).pow 3)).div_const 4 using 1 <;>
    norm_num

theorem actual_gradient (x : ℝ) : gradient P x = (3-3*x^2)/4 :=
  (derivative x).hasGradientAt'.gradient

def entropy (q : ℝ → ℝ) : ℝ :=
  (∫ x, (q x)^2 * Real.log ((q x)^2) ∂sigma) -
  (∫ x, (q x)^2 ∂sigma) * Real.log (∫ x, (q x)^2 ∂sigma)

def energy (q : ℝ → ℝ) : ℝ := ∫ x, ‖gradient q x‖^2 ∂sigma

theorem entropy_value : entropy P = -(1/2:ℝ)*Real.log (1/2) := by
  unfold entropy
  rw [integral_sigma,integral_sigma]
  norm_num [P]

theorem entropy_positive : 0 < entropy P := by
  rw [entropy_value]
  have h := Real.log_neg (show (0:ℝ)<1/2 by norm_num) (show (1/2:ℝ)<1 by norm_num)
  nlinarith

theorem zero_energy : energy P = 0 := by
  rw [energy,integral_sigma]
  norm_num [actual_gradient]

-- The usual rate convention: alpha*Ent_sigma(q²) <= 2*Dirichlet_sigma(q).
def Admissible (a : ℝ) : Prop := 0 ≤ a ∧ ∀ q : ℝ → ℝ,
  ContDiff ℝ ⊤ q → a*entropy q ≤ 2*energy q

theorem zero_admissible : Admissible 0 := by
  refine ⟨le_rfl, ?_⟩
  intro q hq
  have h : 0 ≤ energy q := integral_nonneg (fun x => sq_nonneg ‖gradient q x‖)
  simp only [zero_mul]
  linarith

theorem no_positive_constant (a : ℝ) (ha : 0 < a) : ¬ Admissible a := by
  intro h
  have hh := h.2 P smooth
  rw [zero_energy] at hh
  have hp := entropy_positive
  nlinarith

theorem admissible_set : {a:ℝ | Admissible a} = {0} := by
  ext a
  constructor
  · intro h
    have hzero : a=0 := by
      by_contra hn
      exact no_positive_constant a (lt_of_le_of_ne h.1 (Ne.symm hn)) h
    simpa using hzero
  · intro h
    have ha : a=0 := h
    rw [ha]
    exact zero_admissible

def optimalConstant : ℝ := sSup {a:ℝ | Admissible a}

theorem actual_alpha : optimalConstant = 0 := by
  rw [optimalConstant,admissible_set]
  simp

theorem lower_bound_fails (c : ℝ) (hc : 0 < c) :
    ¬ c / surfaceVolumeRatio ≤ optimalConstant := by
  rw [ratio_one,actual_alpha,div_one]
  exact not_le_of_gt hc

end BoundaryLSICounterexample
#print axioms BoundaryLSICounterexample.body
#print axioms BoundaryLSICounterexample.surface_eq
#print axioms BoundaryLSICounterexample.sigma_mass
#print axioms BoundaryLSICounterexample.actual_gradient
#print axioms BoundaryLSICounterexample.entropy_positive
#print axioms BoundaryLSICounterexample.zero_energy
#print axioms BoundaryLSICounterexample.actual_alpha
#print axioms BoundaryLSICounterexample.lower_bound_fails
