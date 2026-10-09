import Mathlib.Algebra.Algebra.Spectrum.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Normed.Operator.Compact
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Tactic

noncomputable section
open scoped Matrix ComplexOrder Topology
namespace SpectralDisplacement
abbrev M := Matrix (Fin 2) (Fin 2) ℂ

def A (t : ℝ) : M := !![0,(t:ℂ)^2;0,0]
def E : M := !![0,0;1,0]
def Q : M := Matrix.diagonal ![1,0]

theorem gram_positive (B : M) : (Bᴴ*B).PosSemidef := by
  simpa using (Matrix.PosSemidef.one : (1:M).PosSemidef).conjTranspose_mul_mul_same B
def modulus (B : M) : M := (gram_positive B).sqrt

theorem perturbation_gram : Eᴴ*E=Q := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [E,Q,Matrix.mul_apply,Fin.sum_univ_two,Matrix.conjTranspose_apply]

theorem Q_positive : Q.PosSemidef := by
  apply Matrix.PosSemidef.diagonal
  intro i
  fin_cases i <;> norm_num

theorem perturbation_modulus : modulus E=Q := by
  symm
  apply Q_positive.eq_sqrt_of_sq_eq (gram_positive E)
  rw [perturbation_gram]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Q,pow_two,Matrix.mul_apply,Fin.sum_univ_two]

/-- The singular values are the nonnegative eigenvalues of the canonical modulus. -/
theorem singular_spectrum : spectrum ℂ (modulus E)={(1:ℂ),0} := by
  rw [perturbation_modulus]
  ext z
  simp [spectrum.mem_iff,Matrix.isUnit_iff_isUnit_det,Matrix.det_fin_two,
    Matrix.algebraMap_eq_diagonal,Q,isUnit_iff_ne_zero,mul_eq_zero,sub_eq_zero,add_eq_zero_iff_eq_neg]
  tauto

theorem singular_eigenbasis :
    modulus E *ᵥ (![1,0] : Fin 2 → ℂ)=![1,0] ∧
    modulus E *ᵥ (![0,1] : Fin 2 → ℂ)=0 := by
  rw [perturbation_modulus]
  constructor <;> ext i <;> fin_cases i <;> simp [Q,Matrix.mulVec_diagonal]

/-- Compactness of the genuine matrix action on the finite-dimensional complex space. -/
theorem perturbation_compact : IsCompactOperator E.mulVec := by
  have hc : Continuous E.mulVec := by
    change Continuous (fun x : Fin 2 → ℂ => E *ᵥ x)
    fun_prop
  refine ⟨E.mulVec '' Metric.closedBall (0 : Fin 2 → ℂ) 1,
    (isCompact_closedBall _ _).image hc, ?_⟩
  apply Filter.mem_of_superset (Metric.closedBall_mem_nhds (0 : Fin 2 → ℂ) zero_lt_one)
  intro x hx
  exact ⟨x,hx,rfl⟩

theorem original_spectrum (t : ℝ) : spectrum ℂ (A t)={0} := by
  ext z
  simp [spectrum.mem_iff,Matrix.isUnit_iff_isUnit_det,Matrix.det_fin_two,
    Matrix.algebraMap_eq_diagonal,A,isUnit_iff_ne_zero]

theorem perturbed_spectrum (t : ℝ) : spectrum ℂ (A t+E)={(t:ℂ),-(t:ℂ)} := by
  ext z
  have hd : (algebraMap ℂ M z-(A t+E)).det=(z-t)*(z-(-t)) := by
    simp [Matrix.det_fin_two,Matrix.algebraMap_eq_diagonal,A,E]
    ring
  simp [spectrum.mem_iff,Matrix.isUnit_iff_isUnit_det,hd,isUnit_iff_ne_zero,
    mul_eq_zero,sub_eq_zero,add_eq_zero_iff_eq_neg]
  tauto

theorem original_isolated (t : ℝ) :
    ∃ r>0, Metric.ball (0:ℂ) r ∩ spectrum ℂ (A t)={0} := by
  rw [original_spectrum]
  exact ⟨1,zero_lt_one,by simp⟩

theorem perturbed_isolated (t : ℝ) (z : ℂ) (hz : z∈spectrum ℂ (A t+E)) :
    ∃ r>0, Metric.ball z r ∩ spectrum ℂ (A t+E)={z} := by
  rw [perturbed_spectrum] at hz ⊢
  letI : Finite ({(t:ℂ),-(t:ℂ)} : Set ℂ) := (Set.toFinite _).to_subtype
  exact Metric.exists_ball_inter_eq_singleton_of_mem_discrete hz

/-- Distance from the displaced eigenvalue to the entire original spectrum. -/
theorem displacement_exact (t : ℝ) (ht : 0≤t) :
    Metric.infDist (t:ℂ) (spectrum ℂ (A t))=t := by
  rw [original_spectrum,Metric.infDist_singleton]
  simp [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ht]

theorem unbounded_displacement : ∀ C : ℝ, ∃ t : ℝ,
    0<t ∧ (t:ℂ)∈spectrum ℂ (A t+E) ∧
    C<Metric.infDist (t:ℂ) (spectrum ℂ (A t)) := by
  intro C
  refine ⟨|C|+1,by positivity,?_,?_⟩
  · rw [perturbed_spectrum]; simp
  · rw [displacement_exact _ (by positivity)]
    linarith [le_abs_self C]

theorem no_finite_perturbation_only_bound : ¬ ∃ C : ℝ,
    ∀ t>0, ∀ z∈spectrum ℂ (A t+E), Metric.infDist z (spectrum ℂ (A t))≤C := by
  rintro ⟨C,hC⟩
  obtain ⟨t,ht,hz,hd⟩ := unbounded_displacement C
  exact (not_lt_of_ge (hC t ht t hz)) hd

#print axioms perturbation_gram
#print axioms perturbation_modulus
#print axioms singular_spectrum
#print axioms singular_eigenbasis
#print axioms perturbation_compact
#print axioms original_spectrum
#print axioms perturbed_spectrum
#print axioms original_isolated
#print axioms perturbed_isolated
#print axioms displacement_exact
#print axioms unbounded_displacement
#print axioms no_finite_perturbation_only_bound
end SpectralDisplacement
