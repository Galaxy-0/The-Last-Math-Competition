import Mathlib.Algebra.Algebra.Spectrum.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

noncomputable section
open scoped Matrix
namespace MarkovFundamental
abbrev M := Matrix (Fin 2) (Fin 2) ℂ

def realP : Matrix (Fin 2) (Fin 2) ℝ := !![3/4,1/4;1/4,3/4]
def pi : Fin 2 → ℝ := fun _ => 1/2
def P : M := realP.map (algebraMap ℝ ℂ)
def stationaryProjection : M := fun _ j => pi j
/-- The canonical nonsingular matrix inverse, not an assigned answer. -/
def Z : M := (1-P+stationaryProjection)⁻¹

theorem transition_positive (i j : Fin 2) : 0<realP i j := by
  fin_cases i <;> fin_cases j <;> norm_num [realP]
theorem transition_rows (i : Fin 2) : ∑ j,realP i j=1 := by
  fin_cases i <;> norm_num [realP,Fin.sum_univ_two]
theorem lazy (i : Fin 2) : (1:ℝ)/2≤realP i i := by
  fin_cases i <;> norm_num [realP]
theorem stationary_probability : (∀ i,0<pi i) ∧ ∑ i,pi i=1 := by
  constructor
  · intro i; norm_num [pi]
  · norm_num [pi,Fin.sum_univ_two]
theorem stationary (j : Fin 2) : ∑ i,pi i*realP i j=pi j := by
  fin_cases j <;> norm_num [realP,pi,Fin.sum_univ_two]
theorem reversible (i j : Fin 2) : pi i*realP i j=pi j*realP j i := by
  fin_cases i <;> fin_cases j <;> norm_num [realP,pi]

theorem canonical_inverse : Z=!![(3:ℂ)/2,-1/2;-1/2,3/2] := by
  apply Matrix.inv_eq_left_inv
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [P,realP,stationaryProjection,pi,Matrix.mul_apply,Fin.sum_univ_two]

theorem transition_spectrum : spectrum ℂ P={(1:ℂ),1/2} := by
  ext z
  have hd : (algebraMap ℂ M z-P).det=(z-1)*(z-1/2) := by
    simp [Matrix.det_fin_two,Matrix.algebraMap_eq_diagonal,P,realP]
    ring
  simp [spectrum.mem_iff,Matrix.isUnit_iff_isUnit_det,hd,isUnit_iff_ne_zero,
    mul_eq_zero,sub_eq_zero]
  tauto

theorem fundamental_spectrum : spectrum ℂ Z={(1:ℂ),2} := by
  ext z
  have hd : (algebraMap ℂ M z-Z).det=(z-1)*(z-2) := by
    rw [canonical_inverse]
    simp [Matrix.det_fin_two,Matrix.algebraMap_eq_diagonal]
    ring
  simp [spectrum.mem_iff,Matrix.isUnit_iff_isUnit_det,hd,isUnit_iff_ne_zero,
    mul_eq_zero,sub_eq_zero]
  tauto

theorem arithmetic_complement :
    (fun z : ℂ => 1-z) '' spectrum ℂ P={(0:ℂ),1/2} := by
  rw [transition_spectrum]
  norm_num [Set.image_insert_eq,Set.image_singleton]

theorem not_arithmetic_complement :
    spectrum ℂ Z≠(fun z : ℂ => 1-z) '' spectrum ℂ P := by
  rw [fundamental_spectrum,arithmetic_complement]
  intro h
  have he : (2:ℂ)∈({(0:ℂ),1/2} : Set ℂ) := h ▸ (by simp)
  norm_num at he

theorem not_set_complement : spectrum ℂ Z≠(spectrum ℂ P)ᶜ := by
  intro h
  have hz : (1:ℂ)∈spectrum ℂ Z := by rw [fundamental_spectrum]; simp
  have hp : (1:ℂ)∈spectrum ℂ P := by rw [transition_spectrum]; simp
  exact (h ▸ hz) hp

/-- Removing the stationary part still leaves the nontrivial eigenvalue 2. -/
theorem deviation_spectrum : spectrum ℂ (Z-stationaryProjection)={(0:ℂ),2} := by
  ext z
  have hd : (algebraMap ℂ M z-(Z-stationaryProjection)).det=z*(z-2) := by
    rw [canonical_inverse]
    simp [Matrix.det_fin_two,Matrix.algebraMap_eq_diagonal,stationaryProjection,pi]
    ring
  simp [spectrum.mem_iff,Matrix.isUnit_iff_isUnit_det,hd,isUnit_iff_ne_zero,
    mul_eq_zero,sub_eq_zero]
  tauto

theorem reciprocal_nontrivial :
    (fun z : ℂ => (1-z)⁻¹) '' ((spectrum ℂ P) \ {1})={2} := by
  rw [transition_spectrum]
  have he : ({(1:ℂ),1/2} : Set ℂ) \ {1}={1/2} := by ext z; simp
  rw [he]
  norm_num

theorem row_sum (i : Fin 2) : ∑ j,Z i j=1 := by
  rw [canonical_inverse]
  fin_cases i <;> norm_num [Fin.sum_univ_two]

theorem counterexample : (∀ i j,0<realP i j) ∧ (∀ i,∑ j,realP i j=1) ∧
    (∀ j,∑ i,pi i*realP i j=pi j) ∧
    spectrum ℂ Z≠(fun z : ℂ => 1-z) '' spectrum ℂ P :=
  ⟨transition_positive,transition_rows,stationary,not_arithmetic_complement⟩

#print axioms transition_positive
#print axioms transition_rows
#print axioms lazy
#print axioms stationary_probability
#print axioms stationary
#print axioms reversible
#print axioms canonical_inverse
#print axioms transition_spectrum
#print axioms fundamental_spectrum
#print axioms not_arithmetic_complement
#print axioms not_set_complement
#print axioms deviation_spectrum
#print axioms reciprocal_nontrivial
#print axioms row_sum
#print axioms counterexample
end MarkovFundamental
